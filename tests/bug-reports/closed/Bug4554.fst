module Bug4554

// The encoding of the whole let-rec expression must depend on n.
let f (n:nat) : (r:nat{r == n}) =
  let rec go (m:nat) : (r:nat{r == n}) = n in
  go n

let f_values () : Lemma (f 0 == 0 /\ f 1 == 1) = ()

[@@expect_failure [19]]
let bug () : Lemma False = assert (f 0 == 0); assert (f 1 == 1)

// Free variables of the let body must be captured too, even when the
// recursive definition itself is closed.
let body_only (n:nat) : (r:nat{r == n}) =
  let rec go (m:nat) : (r:nat{r == m}) = m in
  go n

[@@expect_failure [19]]
let body_only_bug () : Lemma False =
  assert (body_only 0 == 0);
  assert (body_only 1 == 1)

// Capture both a type and a value when the local function itself is returned.
let closure (#a:Type) (x:a) : unit -> Tot (r:a{r == x}) =
  let rec go () : (r:a{r == x}) = x in
  go

let closure_values () : Lemma (closure 0 () == 0 /\ closure true () == true) = ()

[@@expect_failure [19]]
let closure_bug () : Lemma False =
  assert (closure 0 () == 0);
  assert (closure 1 () == 1)

// Mutually recursive bindings, with two captures used by their definitions
// and another used only by the body of the let-rec expression.
let mutual (x y n:nat) : (r:nat{r == x + y}) =
  let rec go (m:nat) : Tot (r:nat{r == x + y}) (decreases m) =
    if m = 0 then x + y else back (m - 1)
  and back (m:nat) : Tot (r:nat{r == x + y}) (decreases m) =
    if m = 0 then x + y else go (m - 1)
  in
  go n

let mutual_values () : Lemma (mutual 0 0 2 == 0 /\ mutual 1 2 3 == 3) = ()

[@@expect_failure [19]]
let mutual_bug () : Lemma False =
  assert (mutual 0 0 2 == 0);
  assert (mutual 1 2 3 == 3)

// Hash-consing must still identify equal expressions in the same environment.
let shared (n:nat) =
  assert ((let rec go (m:nat) : Dv nat = go n in go) ==
          (let rec go (m:nat) : Dv nat = go n in go))
