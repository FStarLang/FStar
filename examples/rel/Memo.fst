(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Memo

open FStar.Classical
open FStar.Squash
open FStar.WellFounded

(* These should be indices of our effect *)
type dom : eqtype = int
type codom : Type = int

type heap = list (dom * codom)

type memo (a:Type) = heap -> M (a * heap)
let return (a:Type) (x:a) : memo a = fun h -> (x, h)
let bind (a b:Type) (m:memo a) (f:a -> memo b) : memo b =
  fun h -> let (x, h) = m h in f x h

let get (x:dom) : memo (option codom) = fun h -> List.assoc x h, h
let put (x:dom) (y:codom) : memo unit = fun h -> (), (x,y)::h

reifiable reflectable total
new_effect {
  MEMO : (a:Type) -> Effect
  with
    repr = memo;
    return = return;
    bind = bind
    ; get = get
    ; put = put
}

(* Specification-less version of the memoization effect *)
effect Memo (a:Type) = MEMO a (fun _ p -> forall z. p z)

(* Access to the whole heap (for verification-debugging purpose) *)
private
let get_heap () : MEMO heap (fun h0 p -> p (h0, h0))
= let f : MEMO?.repr heap (fun h0 p -> p (h0, h0)) = fun h0 -> h0, h0 in
  MEMO?.reflect f


(* Lemmas about lists *)

let rec for_all_prop (#a:Type) (p:a -> Type0) (l:list a) : Tot Type0 (decreases l)
= match l with
  | [] -> True
  | x :: xs -> p x /\ for_all_prop p xs

let rec for_all_prop_assoc_lemma (#a:eqtype) (#b:Type) (x:a) (p : (a * b) -> Tot Type0) (l:list (a*b))
  : Lemma (requires (for_all_prop p l))
    (ensures (match List.assoc x l with Some y -> p (x,y) | _ -> True))
= match l with
  | [] -> ()
  | (x0, y0) :: xs -> if x0 = x then () else for_all_prop_assoc_lemma x p xs

let forall_prop_assoc_lemma2 (#a:eqtype) (#b:Type) (x:a) (y:b) (p : (a * b) -> Tot Type0)
  : Lemma (forall h. for_all_prop p h /\ List.assoc x h == Some y ==> p (x,y))
= let aux h : Lemma (requires (for_all_prop p h /\ List.assoc x h == Some y)) (ensures (p (x,y))) =
    for_all_prop_assoc_lemma x p h
  in
  FStar.Classical.(forall_intro (move_requires aux))

let valid_memo (h:heap) (f:dom -> Tot codom) = for_all_prop (fun (x,y) -> y == f x) h
let valid_memo_preserve (x:dom) (y:codom) (h:heap) (f:dom -> Tot codom)
  : Lemma (requires (y == f x /\ valid_memo h f)) (ensures (valid_memo ((x,y)::h) f))
= ()

let memo_heap (f:dom -> Tot codom) : Type = list (x:dom & y:codom{y == f x})

let rec memo_heap_to_valid_memo (#f:dom -> Tot codom) (h0:memo_heap f)
  : Pure heap (requires True) (ensures (fun h1 -> valid_memo h1 f))
= match h0 with
  | [] -> []
  | (|x,y|)::h0' ->
    (* TODO (to investigate) : removing #f here prevents the fuinction from verifying *)
    (x,y) :: memo_heap_to_valid_memo #f h0'

let rec valid_memo_to_memo_heap (f:dom -> Tot codom) (h0:heap)
  : Pure (memo_heap f) (requires (valid_memo h0 f)) (ensures (fun _ -> True))
= match h0 with
  | [] ->
    (* TODO : putting a type ascription here is not enough and the function does not verify... *)
    let l : memo_heap f = [] in l
  | (x,y)::h0' ->
    assert (y == f x /\ valid_memo h0' f) ;
    (|x,y|)::valid_memo_to_memo_heap f h0'

let rec valid_memo_id_lemma (f:dom -> Tot codom) (h0:heap)
  : Lemma (requires (valid_memo h0 f))
  (ensures (valid_memo h0 f /\ (let h1 = memo_heap_to_valid_memo (valid_memo_to_memo_heap f h0) in h0 == h1)))
= match h0 with
  | [] -> ()
  | (x,y)::h0' -> valid_memo_id_lemma f h0'

let rec memo_heap_id (#f:dom -> Tot codom) (h0:memo_heap f)
  : Lemma (let h1 = valid_memo_to_memo_heap f (memo_heap_to_valid_memo h0) in h0 == h1)
= match h0 with
  | [] -> ()
  | (|x,y|)::h0' -> memo_heap_id #f h0'


(* [f `computes` g] when the memoized function [f] computes the same total/pure *)
(* function as [g] provided the heap contains only [g]-relevant elements *)
let computes (#p:dom -> Tot Type0) ($f: (x:dom{p x} -> Memo codom)) (g:dom -> Tot codom) =
      forall h0. valid_memo h0 g ==> (forall x. p x ==> (let y ,h1 = reify (f x) h0 in y == g x /\ valid_memo h1 g))


noeq
type memo_pack (f:dom -> Tot codom) =
  | MemoPack :
    h0:heap{valid_memo h0 f} ->
    mf:(dom -> Memo codom){mf `computes` f} ->
    memo_pack f

let apply_memo (#f:dom -> Tot codom) (mp:memo_pack f) (x:dom) : Tot (codom * memo_pack f) =
  let MemoPack h0 mf = mp in
  let y, h1 = reify (mf x) h0 in
  y, MemoPack h1 mf


(* noeq *)
(* type memo_pack (f:dom -> Tot codom) = *)
(*   | MemoPack : *)
(*     h0:memo_heap f -> *)
(*     mf:(dom -> Memo codom){mf `computes` f} *)
(*     -> memo_pack f *)

(* let apply_memo (#f:dom -> Tot codom) (mp:memo_pack f) (x:dom) : Tot (codom * memo_pack f) = *)
(*   let MemoPack h0 mf = mp in *)
(*   let y, h1 = reify (mf x) (memo_heap_to_valid_memo h0) in *)
(*   y, MemoPack (valid_memo_to_memo_heap f h1) mf *)


(* Memoization of a pure function with a complete specification *)

let memo_ (f : dom -> Tot codom) (x:dom) : MEMO codom (fun h0 p -> valid_memo h0 f /\ (forall h. valid_memo h f ==> p (f x, h)))
= match MEMO?.get x with
  | Some y ->
    forall_prop_assoc_lemma2 x y (fun (x,y) -> y == f x) ;
    y
  | None ->
    let y = f x in
    MEMO?.put x y ;
    y


(* Specification-less memoization of a pure function and its extrinsic proof *)

(*  *)
let memo_extr (f : dom -> Tot codom) (x:dom) : Memo codom
= match MEMO?.get x with
  | Some y -> y
  | None ->
    let y = f x in
    MEMO?.put x y ;
    y

let memo_extr_lemma (f:dom -> Tot codom) (x:dom) (h0:heap)
  : Lemma (requires (valid_memo h0 f))
    (ensures (let (y, h1) = reify (memo_extr f x) h0 in valid_memo h1 f /\ y == f x))
= match reify (MEMO?.get x) h0 with
  | Some y, h0' -> forall_prop_assoc_lemma2 x y (fun (x,y) -> y == f x)
  | None, h0' -> ()

let memo_extr_computes (f:dom -> Tot codom) : Lemma ((memo_extr f) `computes` f) =
  let phi0 (h0:heap) (vm:squash(valid_memo h0 f)) (x:dom)
    : Lemma (let y, h1 = reify (memo_extr f x) h0 in y == f x /\ valid_memo h1 f) =
    give_proof vm ; memo_extr_lemma f x h0
  in
  forall_impl_intro (fun (h0:heap) (vm:squash(valid_memo h0 f)) -> forall_intro (phi0 h0 vm) <:
    Lemma (forall x. let y, h1 = reify (memo_extr f x) h0 in y == f x /\ valid_memo h1 f))

let to_memo_pack (f : dom -> Tot codom) : Tot (memo_pack f) =
  memo_extr_computes f ;
  MemoPack [] (memo_extr f)


type t (p:dom -> Type0) = x:dom{p x} -> Memo codom

(* Specification-less memoization of a memoized function and its extrinsic proof *)

(*  *)
let memo_extr_p (p:dom -> Type0) (f : t p) (x:dom{p x}) : Memo codom
= match MEMO?.get x with
  | Some y -> y
  | None ->
    let y = f x in
    MEMO?.put x y ;
    y

let memo_extr_p_lemma (p:dom -> Type0) (f: t p) (g:dom -> Tot codom) (h0:heap) (x:dom)
  : Lemma (requires (valid_memo h0 g /\ f `computes` g))
    (ensures (p x ==> (let (y, h1) = reify (memo_extr_p p f x) h0 in y == g x /\ valid_memo h1 g)))
= match reify (MEMO?.get x) h0 with
  | Some y, h0' ->
    forall_prop_assoc_lemma2 x y (fun (x,y) -> y == g x)
  | None, h0' ->
    ()


(* If [f `computes` g] then the memoized version of [f], [memo_extr_p p f] also computes [g] *)
let memo_extr_p_computes (p:dom -> Type0) (f: (x:dom{p x} -> Memo codom)) (g:dom -> Tot codom)
: Lemma (requires (f `computes` g)) (ensures ((memo_extr_p p f) `computes` g))
=
  let open FStar.Squash in
  let phi0 (fcg:squash(f `computes` g)) (h0:heap) (vm : squash (valid_memo h0 g)) (x:dom)
    : Lemma (p x ==> (let y ,h1 = reify (memo_extr_p p f x) h0 in y == g x /\ valid_memo h1 g))
  = give_proof fcg ;
    give_proof vm ;
    memo_extr_p_lemma p f g h0 x
  in
  let phi1 (fcg:squash(f `computes` g)) (h0:heap) () : Lemma (requires (valid_memo h0 g)) (ensures (forall x. p x ==> (let (y, h1) = reify (memo_extr_p p f x) h0 in y == g x /\ valid_memo h1 g))) =
    FStar.Classical.forall_intro (phi0 fcg h0 (get_proof (valid_memo h0 g)))
  in
  let phi2 fcg (h0:heap)
    : Lemma (valid_memo h0 g ==> (forall x. p x ==> (let y ,h1 = reify (memo_extr_p p f x) h0 in y == g x /\ valid_memo h1 g)))
  = FStar.Classical.move_requires (phi1 fcg h0) () in
  FStar.Classical.forall_intro (phi2 (get_proof (f `computes` g)))


(* (*  *) *)
(* let memo_extr (f : dom -> Tot codom) (x:dom) : MEMO codom (fun h0 p -> (forall z. p z)) *)
(* = memo_extr_p (fun _ -> True) f x *)

(* (\* Should work but does not... *\) *)
(* (\* needs induction to prove valid_memo h0 f ==> valid_memo_p h0 (fun _ -> True) f ? *\) *)

(* let memo_extr_lemma (f:dom -> Tot codom) (x:dom) (h0:heap) *)
(*     : Lemma (requires (valid_memo h0 f)) *)
(*       (ensures (let (y, h1) = reify (memo_extr f x) h0 in valid_memo h1 f /\ y == f x)) *)
(* = assert (valid_memo_p h0 (fun _ -> True) f) ; *)
(*   memo_extr_p_lemma (fun _ -> True) f x h0 *)



(* Tentaive approach to memoization of recursive functions *)
(* Given a function [f : x0:dom -> f0:(x:dom{x << x0} -> Tot codom) -> Tot codom] *)
(* we can compute its fixpoint as follow with [fix f] *)

(* AR: investigate this doesn't work with extracted interfaces *)
// let fix (f : (x0:dom -> f0:(x:dom{x << x0} -> Tot codom) -> Tot codom)) (x0:dom) : Tot codom
// = let rec f0 (x:dom{x << x0}) = f x f0 in
//   f x0 f0

(* A first idea would be to extend the fixpoint to a memoized fixpoint but this clearly *)
(* does not work since the [f0] continuation that we would feed to [f] would need *)
(* to have a [Memo] effect and not a total one. *)

(* So instead we introduce a notion of partial result which can be : *)
noeq type partial_result (x0:dom) : Type =

(* Either a terminated computation of type codom *)
| Done : codom -> partial_result x0

(* Or a computation asking for the result of the recursive call on [x] and a continuation [cont] *)
| Need : x:dom{x << x0} -> cont:(codom -> Tot (partial_result x0)) -> partial_result x0

(* The rule [f x << f] is currently not primitive but take as an axiom in FStar.WellFounded *)
(* We define a convenience operator doing the application and ensuring the corresponding decreasing clause *)
unfold
let ( <| ) #x = apply #codom #(fun _ -> partial_result x)


(* We can define the actual total function represented *)
(* by [f : x:dom -> Tot (partial_result x)] with *)
(* [fixp f : dom -> Tot codom] *)

let rec  complete_fixp (f: (x:dom) -> partial_result x) (x:dom) (px:partial_result x)
  : Tot codom (decreases %[x ; 0 ; px])
=
  match px with
  | Done y -> y
  | Need x' cont ->
    complete_fixp f x (cont <| (fixp f x'))

and fixp (f: (x:dom -> Tot (partial_result x))) (x0:dom)
  : Tot codom (decreases %[x0 ; 1 ; ()])
  = complete_fixp f x0 (f x0)


(* Lemmas about partial results *)

noeq type reachable (f: (x0:dom -> partial_result x0)) x0 : partial_result x0 -> Type0 =
| Now : reachable f x0 (f x0)
| Later : x:dom{x << x0} -> cont:(codom -> Tot (partial_result x0)) -> reachable f x0 (Need x cont) -> reachable f x0 (cont (fixp f x))

let rec reachable_lemma f x px (w:reachable f x px)
  : Lemma (requires True)
    (ensures (complete_fixp f x px == fixp f x))
    (decreases w)
= match w with
  | Now -> assert (px == f x) ; assert (complete_fixp f x px == fixp f x)
  | Later x0 cont w' ->
    reachable_lemma f x (Need x0 cont) w'


let rec fpartial_result x (f: (x:dom -> partial_result x)) (px:partial_result x) : Tot Type0 (decreases px) =
  match px with
  | Done y -> y == fixp f x
  | Need x1 cont ->
    fpartial_result x f (cont <| (fixp f x1))


let rec fpartial_result_lemma f x px (w:reachable f x px) : Lemma (requires True) (ensures (fpartial_result x f px)) (decreases px)
= match px with
  | Done y -> reachable_lemma f x px w (* ; assert (y == fixp f x) ;     assert (fpartial_result x f px) *)

  | Need x' cont ->
    let px' = cont <| (fixp f x') in
    fpartial_result_lemma f x px' (Later x' cont w)

let fpartial_result_init_lemma f x
  : Lemma (requires True) (ensures (fpartial_result x f (f x)))
    [SMTPat (fpartial_result x f (f x))]
= fpartial_result_lemma f x (f x) Now

(* Memoization of a recursive functions represented as [f : x:dom -> partial_result x] with a complete spec *)

let valid_memo_rec (h:heap) (f: (x:dom -> Tot (partial_result x))) = for_all_prop (fun (x,y) -> y == fixp f x) h

unfold
let memo_rec_wp (f: (x:dom -> Tot (partial_result x))) (x0:dom) (h0:heap) (p:(codom * heap) -> Type0) : Tot Type0=
  valid_memo_rec h0 f /\ (forall h. valid_memo_rec h f ==> p (fixp f x0, h))

let valid_memo_rec_lemma
  (f: (x:dom -> Tot (partial_result x)))
  (x:dom) (y:codom) (h0:heap)
  : Lemma (requires (valid_memo_rec h0 f /\ List.assoc x h0 == Some y))
    (ensures (y == fixp f x))
= for_all_prop_assoc_lemma x (fun (x,y) -> y == fixp f x) h0


let rec complete_memo_rec (f: (x:dom -> Tot (partial_result x))) (x:dom) (px:partial_result x{fpartial_result x f px})
  : MEMO codom (memo_rec_wp f x) (decreases %[x ; px])
= match px with
  | Done y -> assert (y == fixp f x) ; y
  | Need x' cont ->
    let y : (y:codom{y == fixp f x'}) =
      let h0 = get_heap () in
      assert (valid_memo_rec h0 f) ;
      match MEMO?.get x' with
      | Some y ->
        valid_memo_rec_lemma f x' y h0 ;
        assert (y == fixp f x') ;
        y
      | None ->
        let px' = f x' in
        fpartial_result_lemma f x' px' Now ;
        assert ( %[x' ; px'] << %[x ; px]) ;
        let y = complete_memo_rec f x' (f x') in
        assert (y == fixp f x') ;
        MEMO?.put x' y ;
        y
    in
    assert (y == fixp f x') ;
    let px1 = cont <| y in
    assert (fpartial_result x f px1) ;
    complete_memo_rec f x px1


let memo_rec (f: (x:dom -> Tot (partial_result x))) (x0:dom)
  : MEMO codom (memo_rec_wp f x0)
= match MEMO?.get x0 with
  | Some y ->
    forall_prop_assoc_lemma2 x0 y (fun (x,y) -> y == fixp f x) ;
    y
  | None ->
    (* fpartial_result_lemma f x0 (f x0) Now ; *)
    let y = complete_memo_rec f x0 (f x0) in
    MEMO?.put x0 y ;
    y






(* ****************************************************************************)
(*                                                                            *)
(*        Specification-less memoization of recursive function                *)
(*        and extrinsic proofs (using reification)                            *)
(*                                                                            *)
(* ****************************************************************************)


let p (x:dom) (px:partial_result x) (x':dom) = %[ %[x'; 2 ; ()] ] << %[ %[x; 0 ; px] ]

(*  *)
let rec complete_memo_rec_extr
  (f: (x:dom -> partial_result x))
  (x:dom)
  (px:partial_result x)
  : Memo codom (decreases %[x ; 1 ; px])
=
  match px with
  | Done y -> y
  | Need x' cont ->
    let y = memo_extr_p (p x px) (memo_rec_extr_temp f x px) x' in
    complete_memo_rec_extr f x (cont <| y)

and memo_rec_extr_temp (f: (x:dom -> partial_result x)) (x0:dom) (px0:partial_result x0) (x:dom{p x0 px0 x})
  : Memo codom (decreases %[x0 ; 0 ; px0])
= memo_rec_extr f x

and memo_rec_extr (f: (x:dom -> Tot (partial_result x))) (x0:dom) : Memo codom (decreases %[ x0 ; 2 ; ()])
= complete_memo_rec_extr f x0 (f x0)


let rec complete_memo_rec_extr_computes :
  (f:(x:dom -> partial_result x)) ->
  (x:dom) ->
  (px:partial_result x) ->
  (h0:heap) ->
  Lemma (requires (fpartial_result x f px /\ valid_memo h0 (fixp f)))
    (ensures (let y, h1 = reify (complete_memo_rec_extr f x px) h0 in y == fixp f x /\ valid_memo h1 (fixp f)))
    (decreases %[x ; 1 ; px])
= fun f x px h0 ->
  match px with
  | Done y -> ()
  | Need x' cont ->
    let compute_lemma0 (h0:heap) (vm:squash(valid_memo h0 (fixp f))) (x':dom) (px':squash (p x px x'))
        : Lemma (p x px x' ==> (let y, h1 = reify (memo_rec_extr_temp f x px x') h0 in
                               y == fixp f x' /\ valid_memo h1 (fixp f)))
    = give_proof vm ; give_proof px' ; assert (%[ %[x; 0 ; px] ] << %[ %[x; 1 ; px] ]); memo_rec_extr_computes f x' h0
    in
    let compute_lemma1 (h0:heap) (vm:squash(valid_memo h0 (fixp f)))
      : Lemma (forall x'. p x px x' ==> (let y, h1 = reify (memo_rec_extr_temp f x px x') h0 in y == fixp f x' /\ valid_memo h1 (fixp f)))
    = forall_impl_intro (compute_lemma0 h0 vm)
    in
    forall_impl_intro compute_lemma1 ;
    assert (computes #(p x px) (memo_rec_extr_temp f x px) (fixp f)) ;

    memo_extr_p_computes (p x px) (memo_rec_extr_temp f x px) (fixp f) ;
    let y, h1 = reify (memo_extr_p (p x px) (memo_rec_extr_temp f x px) x') h0 in
    assert (y == fixp f x') ;
    assert (valid_memo h1 (fixp f)) ;
    complete_memo_rec_extr_computes f x (cont <| y) h1
and memo_rec_extr_computes :
  (f:(x:dom -> partial_result x)) ->
  (x:dom) ->
  (h0:heap) ->
  Lemma (requires (valid_memo h0 (fixp f)))
    (ensures (let y, h1 = reify (memo_rec_extr f x) h0 in y == fixp f x /\ valid_memo h1 (fixp f)))
    (decreases %[x ; 2 ; ()])
= fun f x h0 ->
  (* fpartial_result_lemma f x (f x) Now ; *)
  complete_memo_rec_extr_computes f x (f x) h0


let memo_rec_lemma (f:(x:dom) -> partial_result x)
 : Lemma ((memo_rec_extr f) `computes` (fixp f))
=
  let phi0 (h0:heap) (vm:squash(valid_memo h0 (fixp f))) (x:dom)
    : Lemma (let y, h1 = reify (memo_rec_extr f x) h0 in y == fixp f x /\ valid_memo h1 (fixp f))
  = give_proof vm ; memo_rec_extr_computes f x h0
  in
  forall_impl_intro (fun (h0:heap) (vm:squash(valid_memo h0 (fixp f))) -> forall_intro (phi0 h0 vm) <:
    Lemma (forall x. let y, h1 = reify (memo_rec_extr f x) h0 in y == fixp f x /\ valid_memo h1 (fixp f)))


let to_memo_pack_rec (#g:dom -> Tot codom) 
                     (f : (x:dom -> Tot (partial_result x)))
  : Pure (memo_pack g) (requires (g == fixp f)) (ensures (fun _ -> True)) =
  memo_rec_lemma f ;
  MemoPack [] (memo_rec_extr f)


(* ****************************************************************************)
(*                                                                            *)
(*              Proving equality on functions defined with fixp               *)
(*                                                                            *)
(* ****************************************************************************)

(* In order to prove that [fixp f] and [g] are extensionally equalsm *)
(* it is enough to prove that [fix_eq_proof f g] *)

let rec complete_fixp_eq_proof
  (f: (x:dom -> Tot (partial_result x)))
  (g:dom -> Tot codom)
  (x:dom)
  (px:partial_result x)
  : Type0
=
  match px with
  | Done y -> y == g x
  | Need x1 cont ->
    fixp f x1 == g x1 ==> complete_fixp_eq_proof f g x (cont <| (fixp f x1))

unfold
let fixp_eq_proof f g = forall x. complete_fixp_eq_proof f g x (f x)


let rec complete_fixp_eq
  (f: (x:dom -> Tot (partial_result x)))
  (g:dom -> Tot codom)
  (x:dom)
  (px:partial_result x)
  : Lemma (requires (fpartial_result x f px /\
                    complete_fixp_eq_proof f g x px /\
                    (forall x0. complete_fixp_eq_proof f g x0 (f x0))))
                    (ensures (fixp f x == g x))
                    (decreases %[x ; 0 ; px])
=
  match px with
  | Done y -> ()
  | Need x1 cont ->
    fixp_eq' f g x1 ; complete_fixp_eq f g x (cont <| (fixp f x1))

and fixp_eq'
  (f: (x:dom -> Tot (partial_result x)))
  (g:dom -> Tot codom)
  (x:dom)
  : Lemma (requires (fixp_eq_proof f g))
    (ensures (fixp f x == g x))
    (decreases %[x ; 1 ; ()])
=
  complete_fixp_eq f g x (f x)


let fixp_eq (f: (x:dom -> Tot (partial_result x))) (g:dom -> Tot codom)
  : Lemma (requires (fixp_eq_proof f g)) (ensures (forall x. fixp f x == g x))
=
  let h = get_proof (fixp_eq_proof f g) in
  let f x : Lemma (fixp f x = g x) = give_proof h ; fixp_eq' f g x in
  forall_intro f


(* ****************************************************************************)
(*                                                                            *)
(*                            Example section                                 *)
(*                                                                            *)
(* ****************************************************************************)

let fibonnacci_partial (x:dom) : (partial_result x) =
  if x <= 1
  then Done 1
  else Need (x - 1) (fun y1 -> Need (x - 2) (fun y2 -> Done (y1 + y2)))

unfold
let fibonnacci_ = fixp fibonnacci_partial

unfold
let fibonnacci_memo = memo_rec_extr fibonnacci_partial

let rec fibonnacci (x:dom) =
  if x <= 1
  then 1
  else fibonnacci (x - 1) + fibonnacci (x - 2)



let fibo_complete_fixp_eq_proof (x:dom)
: Lemma (complete_fixp_eq_proof fibonnacci_partial fibonnacci x (fibonnacci_partial x))
=
  let fibp = fibonnacci_partial in
  let fib = fibonnacci in
  let fixfib = fixp fibp in
  let res y = complete_fixp_eq_proof fibp fib x y in
  if x <= 1 then ()
  else match fibp x with
  | Need x1 cont1 ->
    let f1 () : Lemma (requires (fixfib x1 == fib x1)) (ensures (res (cont1 (fixfib x1)))) =
      match cont1 (fixfib x1) with
      | Need x2 cont2 ->
        let f2 () : Lemma (requires (fixfib x2 = fib x2)) (ensures (res (cont2 (fixfib x2)))) =
          match cont2 (fixfib x2) with | Done y -> assert (y == fixfib x1 + fixfib x2 /\ y == fib x1 + fib x2)
        in
        move_requires f2 ()
    in
    move_requires f1 ()

let fibonnacci_partial_induces_fibonnacci () : Lemma (forall x. fibonnacci_ x == fibonnacci x) =
  forall_intro fibo_complete_fixp_eq_proof ; fixp_eq fibonnacci_partial fibonnacci

unfold
let computes_body (f:dom -> Memo codom) (g:dom -> Tot codom) (h0:heap) (x:dom) =
  let (y, h1) = reify (f x) h0 in y == g x /\ valid_memo h1 g

let rec valid_memo_extensionality g0 g1 h : Lemma (requires (forall x. g0 x == g1 x) /\ valid_memo h g0) (ensures (valid_memo h g1)) (decreases h)
=
  match h with
  | [] -> ()
  | x :: xs -> valid_memo_extensionality g0 g1 xs


let computes_extensionality (f : (x:dom -> Memo codom))
                            (g0 g1: dom -> Tot codom)
  : Lemma (requires (f `computes` g0 /\ (forall x. g0 x == g1 x))) (ensures (f `computes`g1))
=
  let phi (h0:heap) (vm:squash(valid_memo h0 g0)) (x:dom) : Lemma (computes_body f g1 h0 x) =
    give_proof vm ; assert (computes_body f g0 h0 x) ; assert (g0 x == g1 x) ;
    let (y, h1) = reify (f x) h0 in valid_memo_extensionality g0 g1 h1
  in
  let phi' (h0:heap) (vm:squash(valid_memo h0 g1)) : Lemma (forall x. computes_body f g1 h0 x) =
    give_proof vm; valid_memo_extensionality g1 g0 h0 ;
    forall_intro (phi h0 (get_proof (valid_memo h0 g0)))
  in
  forall_impl_intro phi'


let fibonnacci_memo_computes_fibonnacci () : Lemma (fibonnacci_memo `computes` fibonnacci) =
  memo_rec_lemma fibonnacci_partial ;
  fibonnacci_partial_induces_fibonnacci () ;
  computes_extensionality fibonnacci_memo fibonnacci_ fibonnacci

let fibo : memo_pack fibonnacci =
  fibonnacci_memo_computes_fibonnacci () ;
  MemoPack [] fibonnacci_memo


(* let _ = *)
(*   let x, _ = apply_memo fibo 7 in *)
(*   assert (x = 21) *)


(* Once we have indexed effects the following definitions might be interesting *)

(* The definition below is pretty close to what is presented in *)
(*   Conor McBride: Turing-Completeness Totally Free. MPC 2015: 257-275 *)
(* but a little more awkward. It would be nice to define McBride's version *)
(* of the monad but in order to do so we need a good treatment of inductives *)
(* and recursion within DM4F. *)

let partial (x:dom) (a:Type) = (a -> M (partial_result x)) -> M (partial_result x)

let return_partial (* (dom:Type) *) (x0:dom) (a:Type) (y:a) : partial x0 a = fun g -> g y
let bind_partial (* (dom:Type) *)
  (x0:dom)
  (a b:Type)
  (m:partial x0 a)
  (f:a -> partial x0 b)
  : partial x0 b
=
  fun g -> m (fun y -> f y g)


(* The definition goes through but it won't be usable until we finish implementing indexed effects *)
total reifiable reflectable
new_effect {
  PARTIAL (* (dom:Type) *) (x:dom) : (a:Type) -> Effect
  with repr = partial x
     ; bind = bind_partial x
     ; return = return_partial x
  }


(* PARTIAL?.repr : *)
(*   x:dom -> *)
(*   a:Type -> *)
(*   wp_a:((a -> ((partial_result x) -> Type0) -> Type0) -> ((partial_result x) -> Type0) -> Type0) -> *)
(*   Tot Type *)
(* = fun x a wp_a -> *)
(*     wp:(a -> (partial_result x -> Type0) -> Type0) -> *)
(*     (x':a -> PURE (partial_result x) wp x') -> *)
(*     PURE (partial_result x) (wp_a wp) *)


(* let run (x0:dom) (m :unit -> PARTIAL x0 codom (fun _ _ -> True)) : partial_result x0 = reify (m ()) (fun y -> Done y) *)
(* TODO : generalize slightly the type partial_result to have wps in continuations *)
(* let recursive_call (#x0:dom) (x:dom{x << x0}) : PARTIAL x0 (fun _ _ -> True) = *)
(*   let need (wp:codom -> (partial_result x0 -> Type0) -> Type0) (g: y:codom -> PURE (partial_result x) (wp y)) *)
(*     : PURE (partial_result x) (fun _ -> True) *)
(*   = Need x g *)
(*   in *)
(*   reflect need *)

(* Then we should be able to define fibonnacci as follows *)
(* let f (x:dom) : partial_result x = *)
(*   run (reify ( *)
(*     if x <= 1 *)
(*     then 0 *)
(*     else *)
(*       let y1 = recursive_call (x - 1) in *)
(*       let y2 = recursive_call (x - 2) in *)
(*       y1 + y2 *)
(*   )) *)





(* Various (unsuccessful) tentative to have a cleaner proof of equality for fixp *)

(* #set-options "--__no_positivity" *)

(* noeq type erpr1 *)
(*   (f:x:dom -> Tot (partial_result x)) *)
(*   (g:dom -> Tot codom) *)
(*   (x:dom) : *)
(*   (px:partial_result x) -> Type *)
(* = *)
(*   | W : px:(partial_result x) -> *)
(*     begin match px with *)
(*     | Done y -> (y':codom{y' == y} -> Lemma (y' == g x)) *)
(*     | Need x1 cont -> (x1':dom{x1' == x1} -> cont':(codom -> Tot (partial_result x)){cont' == cont} -> y1:codom{y1 == fixp f x1} -> Pure (erpr1 f g x (cont' y1)) (requires (y1 == g x1)) (ensures (fun _ -> True))) *)
(*     end -> erpr1 f g x px *)


(* let fibo_erpr (x:dom) : erpr1 fibonnacci_partial fibonnacci x (fibonnacci_partial x) = *)
(*   if x <= 1 then W (normalize_term (fibonnacci_partial x)) (fun y -> assert (y == 0 /\ y == fibonnacci x)) *)
(*   else *)
(*     W (fibonnacci_partial x) (fun x1 cont1 y1 -> *)
(*       W #fibonnacci_partial #fibonnacci #x (cont1 y1) (fun x2 cont2 y2 -> *)
(*         W #fibonnacci_partial #fibonnacci #x (cont2 y2) (fun y -> assert (y == y1 + y2 /\ y1 + y2 == fibonnacci x1 + fibonnacci x2)))) *)

(* noeq type erpr *)
(*   (f:x:dom -> Tot (partial_result x)) *)
(*   (g:dom -> Tot codom) *)
(*   (x:dom) *)
(*   : partial_result x -> Type *)
(* = *)
(*   | PDone : #y:codom -> (y':codom{y' == y} -> Lemma (y' == g x)) -> erpr f g x (Done y) *)
(*   | PNeed : #x1:dom{x1 << x} -> #cont:(codom -> Tot (partial_result x)) -> *)
(*              -> *)
(*             erpr f g x (Need x1 cont) *)


(* let fibo_erpr (x:dom) : erpr fibonnacci_partial fibonnacci x (fibonnacci_partial x) = *)
(*   if x <= 1 then PDone (fun y -> assert (y == 0 /\ y == fibonnacci x)) *)
(*   else *)
(*     PNeed #_ #_ #_ #(x - 1) #_ (fun x1 cont1 y1 -> *)
(*       PNeed #_ #_ #_ #(x-2) #_ (fun x2 cont2 y2 -> *)
(*         PDone #_ #_ #_ #(y1+y2) (fun y -> assert (y == y1 + y2 /\ y1 + y2 == fibonnacci x1 + fibonnacci x2)))) *)

