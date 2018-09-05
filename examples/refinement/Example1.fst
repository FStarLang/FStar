module Example1
open FStar.Integers
module H=HighComp
module L = LowComp

effect HighMon (a:Type) (wp:H.hwp_mon a) = H.HIGH a wp

effect Hi (a:Type)
          (pre: HighComp.state -> Type)
          (post: HighComp.state -> a -> HighComp.state -> Type) =
       HighMon a (fun s0 k -> pre s0  /\ (forall x s1. post s0 x s1 ==> k (x, s1)))

let morph #a (#wp:H.hwp_mon a) ($c:H.HIGH?.repr a wp) : L.lcomp_wp a wp c =
   L.morph #a wp c

// let low_return () : L.lcomp_wp bool _ _ = morph (reify (test_return ()))

open FStar.Tactics

effect HTot (a:Type) = HighComp.HIGH a (fun s post -> forall x. post x)
let test_return () : HTot bool = true
// assume val eq_any : #a:Type -> #b:Type -> x:a -> y:b -> Lemma (x === y)
// #set-options "--debug Example1 --debug_level Rel"
// let test =
//     assert (reify (test_return ()) === H.return_elab true)
//         by (apply_lemma (`eq_any))


let test =
    assert (LowComp.morph #_ _ (H.return_elab true) == L.lreturn true)
        by (dump "A"; apply_lemma (`L.morph_return); dump "B") //spawns SMT proof of monotonicity

let test2 =
    assert (LowComp.morph #_ _ (H.hread_elab 0) == L.lread' 0)
        by (apply_lemma (`L.morph_read))

let test3 (#a:Type0) (#b:Type0)
          (#wpa:H.hwp_mon a) (#wpb: (a -> H.hwp_mon b))
          (c1:H.comp_wp a wpa) (c2: (x:a -> H.comp_wp b (wpb x))) =
    assert (LowComp.morph #_ _ (H.bind_elab c1 c2) == L.lbind (morph c1) (fun x -> morph (c2 x)))
        by (apply_lemma (`L.morph_bind))

open FStar.FunctionalExtensionality


let apply_feq2_lem #a #b #c ($f $g : a -> b -> c) : Lemma (requires (forall x y. f x y == g x y))
                                                        (ensures (f == g)) =
    assert (forall x. feq (f x) (g x));
    assert (feq f g)


let apply_feq_lem #a #b ($f $g : a -> b) : Lemma (requires (forall x. f x == g x))
                                                (ensures (f == g)) =
    assert (feq f g)

let fext () = apply_lemma (`apply_feq_lem); dismiss (); ignore (forall_intros ())

let morph_bind () = dump "A"; fext (); dump "B"; apply_lemma (`L.morph_bind)

#set-options "--debug Example1 --debug_level Rel"
//[@(postprocess_with morph_bind)]
let test4 (#a:Type0)
          (#b:Type0)
          (#wpa:H.hwp_mon a)
          (#wpb: (a -> H.hwp_mon b))
          (c1:H.comp_wp a wpa)
           =
    assert ((fun (c2: (x:a -> H.comp_wp b (wpb x))) ->
              LowComp.morph #b (H.bind_wp wpa wpb) (H.bind_elab c1 c2)) ==
            (fun (c2: (x:a -> H.comp_wp b (wpb x))) -> L.lbind (morph c1) (fun x -> morph (c2 x))))
       by (dump "A"; fext(); dump "B")

    // assert (morph (H.bind_elab c1 c2) === L.lbind (morph c1) (fun x -> morph (c2 x)))
    //     by (apply_lemma (`L.morph_bind))

// let swap : comp_wp unit _ =
//   bind_elab (get_action 0) (fun x0 0

// let sum_and_swap () : Hi uint_32
//     (requires (fun (x0, x1) -> ok (+) x0 x1))
//     (ensures (fun _ _ _ -> True)) =
//    let x0 = H.get_action 0 in
//    let x1 = H.get_action 1 in
//    H.put_action 0 x1;
//    H.put_action 1 x0;
//    x0 + x1

// // let test2 = morph (reify (sum_and_swap ()))
