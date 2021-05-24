module Match.Returns

let test (n: nat) =
  match n returns nat with
  | 0 -> n + 1
  | _ -> n + 2

let test2 (n: nat) =
  match n returns Tot nat with
  | 0 -> n + 1
  | _ -> n + 2

let test3 (n: nat) =
  match n returns PURE int (fun p -> forall x. p x) with
  | 0 -> n + 1
  | _ -> n + 2

let test4 (n: nat) =
  match n returns (PURE int (fun p -> forall x. p x)) with
  | 0 -> n + 1
  | _ -> n + 2

