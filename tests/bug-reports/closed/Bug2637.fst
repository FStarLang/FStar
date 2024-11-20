module Bug2637

noeq
type prog (state_t: Type) (action_t: (state_t -> Type)) : state_t -> Type =
  | P: (pre: _) ->  (bool -> action_t pre) ->  prog state_t action_t pre
  | Q: (pre: _) ->  action_t pre ->  prog state_t action_t pre

assume val state (_: nat) : Type0
assume val transition_pre (u: nat) : Tot (state u)

noeq
type action (u: nat) : (state u) -> Type =
  | S: unit -> action u (transition_pre u)

let test0 : prog (state 42) (action 42) (transition_pre 42) =
  (P (transition_pre 42) (fun _ -> S ()))
