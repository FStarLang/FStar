module Bug3353

// true when all elements of a list satisfy a predicate
let rec for_allP (#a:Type) (pre:a -> prop) (l:list a): prop =
  match l with
  | [] -> True
  | h::t -> pre h /\ for_allP pre t


// a type, a predicate on that type, and some values
assume val ty: Type0
assume val pre: ty -> prop

assume val v1: ty
assume val v2: ty
assume val v3: ty

// Given a list of values...
let all_v = [ v1 ]

// ... we define this subtle squashed type...
assume val all_v_pre: squash (norm [delta_only [`%all_v; `%for_allP]; iota; zeta] (for_allP pre all_v))

#push-options "--fuel 0 --ifuel 0"
let test () =
  // ... to have `pre ...` in the global scope, with no fuel. Hooray!
  assert(pre v1)

assume val p : Type0
let test2 (x : squash (p /\ True)) : squash p = ()

