module Bug2635
open FStar.Tactics.V2

//Original report by Benjamin Bonneau
let prove_False
      (pf : False)
      (_  : (pf0 : False) -> (eq2 #(False) pf ()))
  : False
  = pf

//
// This solves the uvar for the pf binder in prove_false to ()
// But that solution is well-typed only under the False hypothesis
// So we typecheck the solution again in environment for the pf uvar,
//   which is empty, and that produces an SMT failure
//
[@@expect_failure [19]]
let absurd : False
  = _ by (// |- ?pf : l_False
          apply (`prove_False);
          let pf0 = intro () in
          // (pf0 : l_False) |- _ : ?pf == ()
          trefl ())

//Using the  gather_explicit_guards_for_resolved_goals primitive
//you can now see that goal explicitly and work on solving from your tactic
// let admit_absurd (_:unit) : False
//   = _ by (// |- ?pf : l_False
//           apply (`prove_False);
//           let pf0 = intro () in
//           // (pf0 : l_False) |- _ : ?pf == ()
//           trefl ();
//           gather_or_solve_explicit_guards_for_resolved_goals();
//           dump "After";
//           tadmit())



// Revised version, not depending on False by Aseem
assume
val p : prop

assume
val q (x:pos) : prop

//the primitive is perhaps more useful in a context like this
assume
val expect_pos (_: (exists (x:pos). q x)) : p

let intro_exists (#a:Type)  (#p:a -> prop) (x:a) (_: (p x)) : (exists (x:a). p x) = ()

let use_pos (x:nat) (xpos: (x > 0)) (hyp: (q x)) =
  assert p by (
    apply (`expect_pos);
    apply (`intro_exists);
    apply (quote hyp)) //the implicit `pos` of intro_exists is solved by unification here to x:nat

// let use_pos2 (x:nat) (xpos:(x > 0)) (hyp:(q x)) =
//   assert p by (
//     apply (`expect_pos);
//     apply (`intro_exists);
//     apply (quote hyp); //the implicit `pos` of intro_exists is solved by unification here to x:nat
//     //can pick up the goal explicitly to prove that x > 0
//     gather_or_solve_explicit_guards_for_resolved_goals ();
//     let _ = implies_intro () in
//     apply (quote xpos))

let use_one (hyp: (q 1)) =
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
let test (pr: p) (f: (unit -> (pr == ()))) : p = pr

[@@expect_failure]
let ugh () 
  : p
  = _ by (
      apply (`test);
      let _ = intro () in
      // dump "A";
      trefl ()
    ) 

let reflexivity (#a:Type) (x: a) : Lemma (x == x) = ()

[@@expect_failure]
let alt ()
  : p
  = _ by (
      apply (`test);
      let _ = intro () in
      apply_lemma (`reflexivity)
    )

let test_lemma (pr: p) (f: (unit -> (pr == ()))) : Lemma p = ()

[@@expect_failure]
let alt2 ()
  : p
  = _ by (
      apply_lemma (`test_lemma);
      let _ = intro () in
      apply_lemma (`reflexivity)
    )


let test2 (x:int) (_: (x > 0)) = 
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

//
//  Few more reports by Benjamin Bonneau
//

let prove_False0
      (e : empty)
      (_ : (e == false_elim ()))
  : False
  = ()

//
// The proof earlier would go through as follows:
//
// apply (`prove_False0) would create two uvars for the
//   arguments of prove_False0
//
// One for the binder e, let's call it ?u_e
// And second for the binder with type, let's call it ?u_sq
//
// (Tactic engine does an optimization where since ?u_e appears in the type
//   of other uvars (?u_sq here), it is not shown as a goal to the user
//   (?u_e is still tracked in the proof state))
//
// So now the user is presented with a goal of type (?u_e == false_elim #empty ())
// Notice that the implicit argument to false_elim is instantiated to empty,
//   simply by the typing of prove_False0 itself
//
// Then trefl () tries to solve it, and sets ?u_e = false_elim #empty ()
//
// EARLIER, we would then typecheck the implicit solution (false_elim #empty ()),
//   using fastpath, it is an application, so we compute its type to be empty,
// ?u_e also has type empty, things check out and we are done
//
// The bug here is that the solution (false_elim #empty ()) is well-typed in a context
//   that has (_:empty) in it,
// It is not well-typed in the context of the uvar ?u_e which is just empty
//
// Fixing this bug requires that
//   false_elim #empty () is well-typed in the empty context,
// Which it is not, and so the proof fails now
//

[@@ expect_failure [19]]
let absurd : False
  = _ by (
    apply (`prove_False0);
    trefl ())

let int_false_elim
      (i : int)
      (_ : False -> (i == false_elim ()))
  : int
  = i

[@@ expect_failure]
let int0 : int
  = _ by (
    apply (`int_false_elim);
    let _ = intro () in trefl ())


let absurd_omega2 (_ : False) : bool
  =
    let omega (b : bool) : bool
      = not ((coerce_eq #bool #(bool -> bool) () b) b)
    in
    omega (coerce_eq #(bool -> bool) #bool () omega)

let build_omega2
      (w : bool)
      (_ : False -> (w == absurd_omega2 ()))
  = w

[@@ expect_failure [19]]
let omega2 : bool
  = _ by (
    apply (`build_omega2);
    let _ = intro () in trefl ())


//
// Variants of above exploits using lemmas
//

let prove_False_lemma
      (pf : False)
      (_  : (pf0 : False) -> (eq2 #(False) pf ()))
  : Lemma False
  = pf

[@@expect_failure [19]]
let absurd : False
  = _ by (apply_lemma (`prove_False_lemma);
          let pf0 = intro () in
          trefl ())

let prove_False0_lemma
      (e : empty)
      (_ : (e == false_elim ()))
  : Lemma False
  = ()

[@@ expect_failure [19]]
let absurd_false0_lemma : False
  = _ by (
    apply_lemma (`prove_False0_lemma);
    trefl ())
