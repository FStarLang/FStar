module FStar.DM4F.Memo

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


let valid_memo (h:heap) (f:dom -> Tot codom) = for_all_prop (fun (x,y) -> y == f x) h
let valid_memo_preserve (x:dom) (y:codom) (h:heap) (f:dom -> Tot codom)
  : Lemma (requires (y == f x /\ valid_memo h f)) (ensures (valid_memo ((x,y)::h) f))
= ()

private
let get_heap () : MEMO heap (fun h0 p -> p (h0, h0))
= let f : MEMO?.repr heap (fun h0 p -> p (h0, h0)) = fun h0 -> h0, h0 in
  MEMO?.reflect f

(* let my_put (x:dom) (y:codom) (f:dom -> Tot codom) : MEMO unit (fun h0 p -> valid_memo h0 f /\ y == f x /\ (valid_memo ((x,y)::h0) f ==> p ((), (x,y)::h0))) *)
(* = let f : MEMO?.repr unit (fun h0 p -> valid_memo h0 f /\ y == f x /\ (valid_memo ((x,y)::h0) f ==> p ((), (x,y)::h0))) = *)
(*     fun h0 -> ((), (x,y)::h0) *)
(*   in *)
(*   MEMO?.reflect f *)


let forall_prop_assoc_lemma2 (#a:eqtype) (#b:Type) (x:a) (y:b) (p : (a * b) -> Tot Type0)
  : Lemma (forall h. for_all_prop p h /\ List.assoc x h == Some y ==> p (x,y))
= let aux h : Lemma (requires (for_all_prop p h /\ List.assoc x h == Some y)) (ensures (p (x,y))) =
    for_all_prop_assoc_lemma x p h
  in
  FStar.Classical.(forall_intro (move_requires aux))

let memo_f (f : dom -> Tot codom) (x:dom) : MEMO codom (fun h0 p -> valid_memo h0 f /\ (forall h. valid_memo h f ==> p (f x, h)))
= match MEMO?.get x with
  | Some y ->
    forall_prop_assoc_lemma2 x y (fun (x,y) -> y == f x) ;
    y
  | None ->
    let y = f x in
    MEMO?.put x y ;
    y

let fix (f : x0:dom -> f0:(x:dom{x << x0} -> Tot codom) -> Tot codom) (x0:dom) : Tot codom
= let rec f0 (x:dom{x << x0}) = f x f0 in
  f x0 f0


noeq type partial_result : dom -> Type =
| Done : x0:dom -> codom -> partial_result x0
| Need : x0:dom -> x:dom{x << x0} -> (codom -> Tot (partial_result x0)) -> partial_result x0


let rec  complete_fixp (f: (x:dom) -> partial_result x) (x:dom) (px:partial_result x) : Tot codom (decreases %[x ; px]) =
  match px with
  | Done _ y -> y
  | Need x0 x' cont ->
    assume (forall y. cont y << cont) ;
    complete_fixp f x (cont (complete_fixp f x' (f x')))

let fixp (f: x:dom -> Tot (partial_result x)) (x0:dom) : Tot codom
  = complete_fixp f x0 (f x0)

noeq type reachable (f: (x:dom) -> partial_result x) x : partial_result x -> Type0 =
    | Now : reachable f x (f x)
    | Later : x0:dom{x0 << x} -> cont:(codom -> Tot (partial_result x)) -> reachable f x (Need x x0 cont) -> reachable f x (cont (fixp f x0))


let rec reachable_lemma f x px (w:reachable f x px)
  : Lemma (requires True)
    (ensures (complete_fixp f x px == fixp f x))
    (decreases w)
= match w with
  | Now -> assert (px == f x) ; assert (complete_fixp f x px == fixp f x)
  | Later x0 cont w' ->
    reachable_lemma f x (Need x x0 cont) w'

let rec fpartial_result x (f: (x:dom) -> partial_result x) (px:partial_result x) : Tot Type0 (decreases px) =
  match px with
  | Done x0 y -> y == fixp f x
  | Need x0 x1 cont ->
    assume (forall y. cont y << cont) ;
    fpartial_result x f (cont (fixp f x1))


let rec fpartial_result_lemma f x px (w:reachable f x px) : Lemma (requires True) (ensures (fpartial_result x f px)) (decreases px)
= match px with
  | Done _ y -> reachable_lemma f x px w (* ; assert (y == fixp f x) ;     assert (fpartial_result x f px) *)

  | Need x1 x' cont -> assume (forall y. cont y << cont) ;
    let px' = cont (fixp f x') in
    fpartial_result_lemma f x px' (Later x' cont w)

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
  | Done _ y -> assert (y == fixp f x) ; y
  | Need x1 x' cont ->
    assert (x1 == x) ;
    let y : (y:codom{y == fixp f x'}) =
      let h0 = get_heap () in
      assert (valid_memo_rec h0 f) ;
      match MEMO?.get x' with
      | Some y ->
        valid_memo_rec_lemma f x' y h0 ;
        (* for_all_prop_assoc_lemma x' (fun (x',y) -> y == fixp f x') h0 ; *)
        (* forall_prop_assoc_lemma2 x' y (fun (x',y) -> y == fixp f x') ; *)
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

(* let fix2 (f : #a:Type -> wp:(dom -> pure_wp (codom * a)) -> x0:dom -> f0:(x:dom{x << x0} -> a -> PURE (codom * a) (wp x)) -> PURE (codom * a) (wp x0)) (x0:dom) : PURE codom (fun p -> forall y. p y) *)
(* = let wp (p:pure_post (codom * unit)) : Type0 = forall (y:codom). p (y, ()) in *)
(*   let rec f0 (x:dom{x << x0}) () : PURE (codom * unit) wp (decreases x) = f #unit (fun _ -> wp) x f0 in *)
(*   fst (f (fun _ -> wp) x0 f0) *)


(* let memo_rec (f : #a:Type -> wp:(dom -> pure_wp (codom * a)) -> x0:dom -> f0:(x:dom{x << x0} -> a -> PURE (codom * a) (wp x)) -> PURE (codom * a) (wp x0)) (x:dom) *)
(*   : MEMO codom (fun h0 p -> valid_memo h0 (fix f) /\ (forall h. valid_memo h (fix f) ==> p (fix f, h))) *)
(* = *)
(*   let rec f0 (x:dom{x << x0}) = *)
(*     match MEMO?.get x with *)
(*     | Some y -> *)
(*       forall_prop_assoc_lemma2 x y (fun (x,y) -> y = (fix f)) ; *)
(*       y *)
(*     | None -> *)
(*       let y = MEMO?.reflect (fun h0 -> f #heap x (reify f0) h0) in *)

