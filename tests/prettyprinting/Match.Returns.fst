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

let test5 (n:nat) =
  match test4 n as y returns Tot (n:nat{n > y}) with
  | 0 -> 0
  | _ -> 1

let test6 (n:nat) =
  match n returns Tot (m:nat{m == n}) with
  | 0 -> 0
  | _ -> 1

let test7 (n:nat) =
  if test4 n > 0 as y returns Tot (n:nat{n > y})
  then 0
  else 1
