module Bug2635
open FStar.Tactics

//Original report by Benjamin Bonneau
let prove_False
      (pf : squash False)
      (_  : (pf0 : squash False) -> squash (eq2 #(squash False) pf ()))
  : squash False
  = pf

//This fails with error 217, correctly complaining that the solved goal does not have type False
[@@expect_failure [217]]
let absurd : squash False
  = _ by (// |- ?pf : squash l_False
          apply (`prove_False);
          let pf0 = intro () in
          // (pf0 : squash l_False) |- _ : ?pf == ()
          trefl ())

//Using the  gather_explicit_guards_for_resolved_goals primitive
//you can now see that goal explicitly and work on solving from your tactic
let admit_absurd (_:unit) : squash False
  = _ by (// |- ?pf : squash l_False
          apply (`prove_False);
          let pf0 = intro () in
          // (pf0 : squash l_False) |- _ : ?pf == ()
          trefl ();
          gather_or_solve_explicit_guards_for_resolved_goals();
          dump "After";
          tadmit())



// Revised version, not depending on False by Aseem
assume
val p : Type0

assume
val q (x:pos) : Type0

//the primitive is perhaps more useful in a context like this
assume
val expect_pos (_: squash (exists (x:pos). q x)) : squash p

let intro_exists (#a:Type)  (#p:a -> Type) (x:a) (_:squash (p x)) : squash (exists (x:a). p x) = ()

[@@expect_failure [217]]
let use_pos (x:nat) (xpos:squash (x > 0)) (hyp:squash (q x)) =
  assert p by (
    apply (`expect_pos);
    apply (`intro_exists);
    apply (quote hyp)) //the implicit `pos` of intro_exists is solved by unification here to x:nat

let use_pos (x:nat) (xpos:squash (x > 0)) (hyp:squash (q x)) =
  assert p by (
    apply (`expect_pos);
    apply (`intro_exists);
    apply (quote hyp); //the implicit `pos` of intro_exists is solved by unification here to x:nat
    //can pick up the goal explicitly to prove that x > 0
    gather_or_solve_explicit_guards_for_resolved_goals ();
    let _ = implies_intro () in
    apply (quote xpos))

let use_one (hyp:squash (q 1)) =
  assert p by (
    apply (`expect_pos);
    apply (`intro_exists);
    apply (quote hyp); //the implicit `pos` of intro_exists is solved by unification here to 1:nat
    //and F* does not accept that implicitly
    //but you can ask F* to solve it by simplification
    gather_or_solve_explicit_guards_for_resolved_goals ())


//////////////////////////////////////////////////////////////
// Some other variants and test cases
//////////////////////////////////////////////////////////////
let test (pr:squash p) (f: (unit -> squash (pr == ()))) : squash p = pr

[@@expect_failure]
let ugh () 
  : squash p
  = _ by (
      apply (`test);
      let _ = intro () in
      dump "A";
      trefl ()
    ) 

let reflexivity (#a:Type) (x: a) : Lemma (x == x) = ()

[@@expect_failure]
let alt ()
  : squash p
  = _ by (
      apply (`test);
      let _ = intro () in
      apply_lemma (`reflexivity)
    )

let test_lemma (pr:squash p) (f: (unit -> squash (pr == ()))) : Lemma p = ()

[@@expect_failure]
let alt2 ()
  : squash p
  = _ by (
      apply_lemma (`test_lemma);
      let _ = intro () in
      apply_lemma (`reflexivity)
    )


let test2 (x:int) (_:squash (x > 0)) = 
  assert (x >= 0 /\ x > 0)
    by (split();
        smt();
        smt())

let rec arrow (args:list Type) (res:Type) = 
  match args with
  | [] -> res
  | hd::tl -> hd -> arrow tl res

let app (arg:Type) (res:Type) (f:arrow [arg] res) (x:arg) : res = f x

let id_int : int -> int = fun x -> x

let some_int : int = _ by (apply (`app); norm [zeta; delta; iota]; apply (`id_int); exact (`0))


let pi : i:int { p } = let _ = assume p in 0

[@@postprocess_with (fun () -> norm [delta]; trefl())]
let pi_norm : i:int { p } = pi
