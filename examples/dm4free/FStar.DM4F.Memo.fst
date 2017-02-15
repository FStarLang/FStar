module FStar.DM4F.Memo

open FStar.Classical
open FStar.Squash

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
new_effect_for_free {
  MEMO : (a:Type) -> Effect
  with
    repr = memo;
    return = return;
    bind = bind
  and effect_actions
      get = get
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

(* [f `computes` g] when the memoized function [f] computes the same total/pure *)
(* function as [g] provided the heap contains only [g]-relevant elements *)
let computes (#p:dom -> Tot Type0) ($f: x:dom{p x} -> Memo codom) (g:dom -> Tot codom) =
      forall h0. valid_memo h0 g ==> (forall x. p x ==> (let y ,h1 = reify (f x) h0 in y == g x /\ valid_memo h1 g))



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

reifiable
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




(* Specification-less memoization of a memoized function and its extrinsic proof *)

reifiable
let memo_extr_p (p:dom -> Type0) (f : x:dom{p x} -> Memo codom) (x:dom{p x}) : Memo codom
= match MEMO?.get x with
  | Some y -> y
  | None ->
    let y = f x in
    MEMO?.put x y ;
    y

let memo_extr_p_lemma (p:dom -> Type0) (f: x:dom{p x} -> Memo codom) (g:dom -> Tot codom) (h0:heap) (x:dom)
  : Lemma (requires (valid_memo h0 g /\ f `computes` g))
    (ensures (p x ==> (let (y, h1) = reify (memo_extr_p p f x) h0 in y == g x /\ valid_memo h1 g)))
= match reify (MEMO?.get x) h0 with
  | Some y, h0' ->
    forall_prop_assoc_lemma2 x y (fun (x,y) -> y == g x)
  | None, h0' ->
    ()


(* If [f `computes` g] then the memoized version of [f], [memo_extr_p p f] also computes [g] *)
let memo_extr_p_computes (p:dom -> Type0) (f: x:dom{p x} -> Memo codom) (g:dom -> Tot codom)
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


(* reifiable *)
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

let fix (f : x0:dom -> f0:(x:dom{x << x0} -> Tot codom) -> Tot codom) (x0:dom) : Tot codom
= let rec f0 (x:dom{x << x0}) = f x f0 in
  f x0 f0

(* A first idea would be to extend the fixpoint to a memoized fixpoint but this clearly *)
(* does not work since the [f0] continuation that we would feed to [f] would need *)
(* to have a [Memo] effect and not a total one. *)

(* So instead we introduce a notion of partial result which can be : *)
noeq type partial_result (x0:dom) : Type =

(* Either a terminated computation of type codom *)
| Done : codom -> partial_result x0

(* Or a computation asking for the result of the recursive call on [x] and a continuation [cont] *)
| Need : x:dom{x << x0} -> cont:(codom -> Tot (partial_result x0)) -> partial_result x0


(* We can define the actual total function represented *)
(* by [f : x:dom -> Tot (partial_result x)] with *)
(* [fixp f : dom -> Tot codom] *)

let rec  complete_fixp (f: (x:dom) -> partial_result x) (x:dom) (px:partial_result x)
  : Tot codom (decreases %[x ; 0 ; px])
=
  match px with
  | Done y -> y
  | Need x' cont ->
    assume (forall y. cont y << cont) ;
    complete_fixp f x (cont (fixp f x'))

and fixp (f: x:dom -> Tot (partial_result x)) (x0:dom)
  : Tot codom (decreases %[x0 ; 1 ; ()])
  = complete_fixp f x0 (f x0)


(* Lemmas about partial results *)

noeq type reachable (f: (x0:dom) -> partial_result x0) x0 : partial_result x0 -> Type0 =
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


let rec fpartial_result x (f: (x:dom) -> partial_result x) (px:partial_result x) : Tot Type0 (decreases px) =
  match px with
  | Done y -> y == fixp f x
  | Need x1 cont ->
    assume (forall y. cont y << cont) ;
    fpartial_result x f (cont (fixp f x1))


let rec fpartial_result_lemma f x px (w:reachable f x px) : Lemma (requires True) (ensures (fpartial_result x f px)) (decreases px)
= match px with
  | Done y -> reachable_lemma f x px w (* ; assert (y == fixp f x) ;     assert (fpartial_result x f px) *)

  | Need x' cont -> assume (forall y. cont y << cont) ;
    let px' = cont (fixp f x') in
    fpartial_result_lemma f x px' (Later x' cont w)



(* Memoization of a recursive functions represented as [f : x:dom -> partial_result x] with a complete spec *)

let valid_memo_rec (h:heap) (f: x:dom -> Tot (partial_result x)) = for_all_prop (fun (x,y) -> y == fixp f x) h

unfold
let memo_rec_wp (f: x:dom -> Tot (partial_result x)) (x0:dom) (h0:heap) (p:(codom * heap) -> Type0) : Tot Type0=
  valid_memo_rec h0 f /\ (forall h. valid_memo_rec h f ==> p (fixp f x0, h))

let valid_memo_rec_lemma
  (f: x:dom -> Tot (partial_result x))
  (x:dom) (y:codom) (h0:heap)
  : Lemma (requires (valid_memo_rec h0 f /\ List.assoc x h0 == Some y))
    (ensures (y == fixp f x))
= for_all_prop_assoc_lemma x (fun (x,y) -> y == fixp f x) h0


let rec complete_memo_rec (f: x:dom -> Tot (partial_result x)) (x:dom) (px:partial_result x{fpartial_result x f px})
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
    assume (forall y. cont y << cont) ;
    let px1 = cont y in
    assert (fpartial_result x f px1) ;
    complete_memo_rec f x px1


let memo_rec (f: x:dom -> Tot (partial_result x)) (x0:dom)
  : MEMO codom (memo_rec_wp f x0)
= match MEMO?.get x0 with
  | Some y ->
    forall_prop_assoc_lemma2 x0 y (fun (x,y) -> y == fixp f x) ;
    y
  | None ->
    fpartial_result_lemma f x0 (f x0) Now ;
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

reifiable
let rec complete_memo_rec_extr
  (f: (x:dom) -> partial_result x)
  (x:dom)
  (px:partial_result x)
  : Memo codom (decreases %[x ; 1 ; px])
=
  match px with
  | Done y -> y
  | Need x' cont ->
    let y = memo_extr_p (p x px) (memo_rec_extr_temp f x px) x' in
    assume (forall y. cont y << cont) ;
    complete_memo_rec_extr f x (cont y)

and memo_rec_extr_temp (f: (x:dom) -> partial_result x) (x0:dom) (px0:partial_result x0) (x:dom{p x0 px0 x})
  : Memo codom (decreases %[x0 ; 0 ; px0])
= memo_rec_extr f x

and memo_rec_extr (f: x:dom -> Tot (partial_result x)) (x0:dom) : Memo codom (decreases %[ x0 ; 2 ; ()])
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
    assume (forall y. cont y << cont) ;
    complete_memo_rec_extr_computes f x (cont y) h1
and memo_rec_extr_computes :
  (f:(x:dom -> partial_result x)) ->
  (x:dom) ->
  (h0:heap) ->
  Lemma (requires (valid_memo h0 (fixp f)))
    (ensures (let y, h1 = reify (memo_rec_extr f x) h0 in y == fixp f x /\ valid_memo h1 (fixp f)))
    (decreases %[x ; 2 ; ()])
= fun f x h0 ->
  fpartial_result_lemma f x (f x) Now ;
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



(* ****************************************************************************)
(*                                                                            *)
(*                            Example section                                 *)
(*                                                                            *)
(* ****************************************************************************)

let fibonnacci_partial (x:dom) : (partial_result x) =
  if x <= 1
  then Done 0
  else Need (x - 1) (fun y1 -> Need (x - 2) (fun y2 -> Done (y1 + y2)))

let fibonnacci_ = fixp fibonnacci_partial

let fibonnacci_memo = memo_rec_extr fibonnacci_partial

let rec fibonnacci (x:dom) =
  if x <= 1
  then 0
  else fibonnacci (x - 1) + fibonnacci (x - 2)

(* let eq_rec_partial_result *)
(*   (f:x:dom -> Tot (partial_result x)) *)
(*   (g:dom -> Tot codom) *)
(*   (x:dom) *)
(*   (px:partial_result x{fpartial_result f x px}) *)
(*   : Type0 *)
(* = *)
(*   match px with *)
(*   | Done y -> y == g x *)
(*   | Need x1 cont -> fixp f x1 == g x1 /\ eq_rec_partial_result f g x (cont (fixp f x1)) *)

(* let eq_rec_fixp (f : (x:dom -> partial_result x)) (g:dom -> Tot codom) *)
(*   : Lemma (requires (forall x0. eq_rec_partial_result f g x (f x0)) *)
(*     (forall x0. fixp f x0 == g x0) *)
(* = *)
(*   let rec f_eq0 (x:dom) (px:partial_result x{fpartial_result f x px})  : Lemma (requires (eq_rec_partial_result f g x px) (ensures (fixp f x == g x)) = *)
(*     match f x with *)
(*     | Done y -> () *)
(*     | Need x1 cont -> f_eq x (cont (fixp f x1)) *)
(*   in *)
(*   let f_eq  *)

(* let rec fibo_equiv (x:dom) : Lemma (fibonnacci_ x == fibonnacci x) = *)
(*   if x <= 1 then () else begin admit () ; fibo_equiv (x - 1) ; fibo_equiv (x - 2) end *)
