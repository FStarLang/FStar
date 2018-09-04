module Example1
open FStar.Integers
module H=HighComp
module L = LowComp

effect HighMon (a:Type) (wp:H.hwp_mon a) = H.HIGH a wp

effect Hi (a:Type)
          (pre: HighComp.state -> Type)
          (post: HighComp.state -> a -> HighComp.state -> Type) =
       HighMon a (fun s0 k -> pre s0  /\ (forall x s1. post s0 x s1 ==> k (x, s1)))

effect HTot (a:Type) = Hi a (fun _ -> True) (fun _ _ _ -> True)

let morph #a (#wp:H.hwp_mon a) ($c:H.HIGH?.repr a wp) : L.lcomp_wp a wp c =
   L.morph #a wp c

let test_return () : HTot bool = true
let low_return () : L.lcomp_wp bool _ _ = morph (reify (test_return ()))

open FStar.Tactics
assume val eq_any : #a:Type -> #b:Type -> x:a -> y:b -> Lemma (x === y)
let test (a:Type) (wp:H.hwp_mon a) (c:H.comp_wp a wp) =
    assert (L.morph wp c === L.lreturn true)
        by (dump "A"; apply_lemma (`L.morph_return); dump "B")


let sum_and_swap () : Hi uint_32
    (requires (fun (x0, x1) -> ok (+) x0 x1))
    (ensures (fun _ _ _ -> True)) =
   let x0 = H.get_action 0 in
   let x1 = H.get_action 1 in
   H.put_action 0 x1;
   H.put_action 1 x0;
   x0 + x1

let test = reify (sum_and_swap ())
let x = HighComp.HIGH?.repr



let test2 = morph (reify (sum_and_swap ()))
