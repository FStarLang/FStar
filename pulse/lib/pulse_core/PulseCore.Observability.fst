module PulseCore.Observability
(*
obs > unobs >----.
                 |
                 v
      ghost > neutral > ghost non_info

ghost info    , neutral info     |> ghost info
ghost non_info, neutral info     |> neutral info
ghost info    , neutral non_info |> ghost non_info
ghost non_info, neutral non_info |> ghost non_info

neutral _, ghost a |> ghost a
*)
type observability =
  | Neutral
  | Observable
  | Unobservable

let at_most_one_observable o1 o2 =
  match o1, o2 with
  | Observable, Observable -> false
  | _ -> true

let join_obs o1 o2 =
  match o1, o2 with
  | Observable, _
  | _, Observable -> Observable
  | Neutral, n
  | n, Neutral -> n
  | _ -> Unobservable
