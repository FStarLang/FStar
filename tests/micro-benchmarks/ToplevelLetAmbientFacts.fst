module ToplevelLetAmbientFacts

/// The result type of a `Pure` computation carries its postcondition, so the
/// *inferred* type of a top-level `let _ = lemma ()` is `squash p` -- and a
/// top-level binding of squash type is published to the solver as an ambient
/// fact, in scope for every query in the rest of the module.
///
/// A `let` whose type the user did not write should not have that effect. The
/// fact appears nowhere in the source, and a module with a table of them (say,
/// a list of `assert_norm`ed test vectors) hands the solver a pile of ground
/// instances to chew on in every later proof.
///
/// So an unannotated top-level `let` records `unit`, and an annotated one gets
/// exactly what it asked for. The `let _ : nonempty t = nonempty_intro w`
/// idiom of tests/error-messages/Nonempty.fst relies on the latter.

assume val phi : prop
assume val lemma_phi (_: unit) : Lemma phi

(* No type written, so nothing is published. *)
let _ = lemma_phi ()

[@@expect_failure [19]]
let anonymous_is_not_ambient (_: unit) : Lemma phi = ()

(* Naming the binding does not make its inferred type any more intentional. *)
assume val psi : prop
assume val lemma_psi (_: unit) : Lemma psi

let named = lemma_psi ()

[@@expect_failure [19]]
let named_is_not_ambient (_: unit) : Lemma psi = ()

(* An ascription is a request, and it is honoured. *)
assume val chi : prop
assume val lemma_chi (_: unit) : Lemma chi

let _ : squash chi = lemma_chi ()

let ascribed_is_ambient (_: unit) : Lemma chi = ()

(* So is a val declaration. *)
assume val theta : prop
assume val lemma_theta (_: unit) : Lemma theta

val declared : squash theta
let declared = lemma_theta ()

let declared_is_ambient (_: unit) : Lemma theta = ()
