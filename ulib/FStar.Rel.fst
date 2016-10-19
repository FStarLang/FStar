module FStar.Rel

open FStar.Squash
open FStar.Classical
open FStar.List.Tot


let rel (a:Type) : Type = a -> a -> Tot Type0

#set-options "--__temp_no_proj FStar.Rel"
noeq type reflexive_transitive_closure (a:Type) (r:rel a) : a -> a -> Type0  =
  | RTCRefl : (x:a) -> reflexive_transitive_closure a r x x
  | RTCTrans : (x:a) -> (y:a) -> (z:a) -> reflexive_transitive_closure a r x y -> reflexive_transitive_closure a r y z -> reflexive_transitive_closure a r x z
  | RTCIncl : (x:a) -> (y:a) -> (r x y) -> reflexive_transitive_closure a r x y


let reflexive_transitive_closure_is_reflexive (#a:Type) (#r:rel a) (x:a)
  : Lemma (requires True) (ensures (reflexive_transitive_closure a r x x))
          [SMTPat (reflexive_transitive_closure a r x x)]
  = give_witness (RTCRefl #_ #r x)


let reflexive_transitive_closure_is_transitive (#a:Type) (#r:rel a) (x:a) (y:a) (z:a)
  : Lemma (requires (reflexive_transitive_closure a r x y /\ reflexive_transitive_closure a r y z))
          (ensures (reflexive_transitive_closure a r x z))
          [SMTPat (reflexive_transitive_closure a r x y /\ reflexive_transitive_closure a r y z)]
  =
  let w0 = get_proof (reflexive_transitive_closure a r x y /\ reflexive_transitive_closure a r y z) in
  (* Version for NewPrims *)
  (* give_proof (map_squash w0 (fun w -> match w with And w1 w2 -> RTCTrans x y z w1 w2)) *)
  let apply_trans (And w1 w2) = RTCTrans #_ #r x y z w1 w2 in
  give_proof (bind_squash w0 (fun w -> map_squash w apply_trans))

let reflexive_transitive_closure_contains_relation (#a:Type) (#r:rel a) (x:a) (y:a)
  : Lemma (requires (r x y)) (ensures (reflexive_transitive_closure a r x y))
    [SMTPat (reflexive_transitive_closure a r x y)]
  = give_proof (map_squash (get_proof (r x y)) (fun w -> RTCIncl #_ #r x y w))


let rec create_from_path (#a:Type) (r:rel a) (l:(list a){length l > 0}) : Tot Type0 (decreases l) =
  match l with
  | [x] -> True
  | [x;y] -> reflexive_transitive_closure a r x y
  | x :: y :: l' -> reflexive_transitive_closure a r x y /\ create_from_path r (y::l')


let rec last (#a:Type) (l:(list a){length l > 0}) : Tot a =
  match l with
  | [x] -> x
  | x::l -> last l

let first (#a:Type) (l:(list a){length l > 0}) : Tot a =
  match l with | x :: _ -> x


let rec create_from_path_lemma (#a:Type) (r:rel a) (l:(list a){length l > 0})
  : Lemma (requires (create_from_path r l)) (ensures (reflexive_transitive_closure a r (first l) (last l)))
  = match l with
  | [x] -> ()
  | [x; y] -> ()
  | x :: y :: l' -> create_from_path_lemma r (y::l')
