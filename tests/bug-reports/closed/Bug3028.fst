module Bug3028

let mk t = unit -> Dv t
let mk2 t = mk t

let _ = assert (mk int == mk2 int)

[@@expect_failure]
let _ = assert (mk int == mk bool)

[@@expect_failure]
let _ = assert (mk int == mk2 bool)

let mka (x:int) : unit -> Dv int = fun () -> x

[@@expect_failure]
let test () =
  assert (mka 1 == mka 2)

assume val st : int -> Type

(* This example can trigger the scoping bug shown in the comment in PR
#3028. The problem is that when we are encoding the arrow `st ii -> Dv
unit`, `ii` is bound to `reveal i`, so when we generate the typing axiom
for this impure arrow, we must not attempt to state the typing in terms of
the encoding ii.

The current patch now just looks at the free variables of the arrows, in
this case `ii` at type `int`, and states that `Non_total_Tm_arrow_...
@x0` has type Type whenever `@x0` has type `int`, without considering
(correctly) the fact that `ii` is `reveal i`.

The encoding of the arrow expression itself is then
`Non_total_Tm_arrow_... (reveal i)`, as this particular _instance_ is
indeed applied to `reveal i`.

The only tricky missing bit in the explanation above is that the types
of the free variables can themselves have free variables. We just
quantify universally over those, without requiring any typing hypothesis.
*)
let t2 : Type =
  i:Ghost.erased int -> Tot (let ii = Ghost.reveal i in st ii -> Dv unit)

(* Force a query *)
let _ = assert (forall x. x+1 > x)
