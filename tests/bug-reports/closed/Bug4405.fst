module Bug4405

(* `eliminate exists` with more binders than
   max_indefinite_description_arity used to be encoded as a nest of
   existentials, one level per indefinite_descriptionN call. When the body is
   a single application of a named predicate, the SMT solver has no good
   trigger for the outer levels of the nest and falls back to a multi-pattern
   of typing hypotheses, enumerating every tuple of terms of the right type.
   All of these must verify at the default rlimit. *)

assume val t : Type0
assume val goal : prop
assume val p1  : t -> prop
assume val p2  : t -> prop
assume val p3  : t -> prop
assume val p4  : t -> prop
assume val p5  : t -> prop
assume val p6  : t -> prop
assume val p7  : t -> prop
assume val p8  : t -> prop
assume val p9  : t -> prop
assume val p10 : t -> prop
assume val p11 : t -> prop

assume val use10 : x1:t -> x2:t -> x3:t -> x4:t -> x5:t ->
                   x6:t -> x7:t -> x8:t -> x9:t -> x10:t ->
  Lemma (requires p1 x1 /\ p2 x2 /\ p3 x3 /\ p4 x4 /\ p5 x5 /\
                  p6 x6 /\ p7 x7 /\ p8 x8 /\ p9 x9 /\ p10 x10)
        (ensures goal)

assume val use11 : x1:t -> x2:t -> x3:t -> x4:t -> x5:t ->
                   x6:t -> x7:t -> x8:t -> x9:t -> x10:t -> x11:t ->
  Lemma (requires p1 x1 /\ p2 x2 /\ p3 x3 /\ p4 x4 /\ p5 x5 /\ p6 x6 /\
                  p7 x7 /\ p8 x8 /\ p9 x9 /\ p10 x10 /\ p11 x11)
        (ensures goal)

let body10 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t) : prop =
  p1 x1 /\ p2 x2 /\ p3 x3 /\ p4 x4 /\ p5 x5 /\
  p6 x6 /\ p7 x7 /\ p8 x8 /\ p9 x9 /\ p10 x10

let body11 (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : t) : prop =
  p1 x1 /\ p2 x2 /\ p3 x3 /\ p4 x4 /\ p5 x5 /\ p6 x6 /\
  p7 x7 /\ p8 x8 /\ p9 x9 /\ p10 x10 /\ p11 x11

(* Two levels of indefinite_description. *)
let folded10 (_ : squash (exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t).
                            body10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10))
  : Lemma goal
= eliminate exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t).
    body10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  with use10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10

(* Three levels: this one used not to return at all. *)
let folded11 (_ : squash (exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : t).
                            body11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11))
  : Lemma goal
= eliminate exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : t).
    body11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
  with use11 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11

(* The inlined form, which was always fine. *)
let inlined10
  (_ : squash (exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t).
                 p1 x1 /\ p2 x2 /\ p3 x3 /\ p4 x4 /\ p5 x5 /\
                 p6 x6 /\ p7 x7 /\ p8 x8 /\ p9 x9 /\ p10 x10))
  : Lemma goal
= eliminate exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : t).
    p1 x1 /\ p2 x2 /\ p3 x3 /\ p4 x4 /\ p5 x5 /\
    p6 x6 /\ p7 x7 /\ p8 x8 /\ p9 x9 /\ p10 x10
  with use10 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
