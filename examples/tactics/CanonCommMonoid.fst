module CanonCommMonoid

open FStar.List
open FStar.Tactics
open FStar.Reflection
open FStar.Classical
open FStar.OrdMap

(* An expression canonizer for commutative monoids
   Inspired by:
   - http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html
   - http://poleiro.info/posts/2015-04-13-writing-reflective-tactics.html
*)

(***** Commutative monoids *)

(* Should eventually go to standard library *)

let right_unitality_lemma (a:Type) (u:a) (mult:a -> a -> a) =
  x:a -> Lemma (x `mult` u == x)

let left_unitality_lemma (a:Type) (u:a) (mult:a -> a -> a) =
  x:a -> Lemma (u `mult` x == x)

let associativity_lemma (a:Type) (mult:a -> a -> a) =
  x:a -> y:a -> z:a -> Lemma (x `mult` y `mult` z == x `mult` (y `mult` z))

let commutativity_lemma (a:Type) (mult:a -> a -> a) =
  x:a -> y:a -> Lemma (x `mult` y == y `mult` x)

unopteq
type cm (a:Type) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    right_unitality:right_unitality_lemma a unit mult ->
    left_unitality:left_unitality_lemma a unit mult ->
    associativity:associativity_lemma a mult ->
    commutativity:commutativity_lemma a mult ->
    cm a

let int_plus_cm : cm int =
  CM 0 (+) (fun x -> ()) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

let int_multiply_cm : cm int =
  CM 1 op_Multiply (fun x -> ()) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

(***** Expression syntax *)

let var : eqtype = nat

type exp : Type =
  | Unit : exp
  | Var : var -> exp
  | Mult : exp -> exp -> exp

let rec exp_to_string (e:exp) : string =
  match e with
  | Unit -> "Unit"
  | Var x -> "Var " ^ string_of_int (x <: var)
  | Mult e1 e2 -> "Mult (" ^ exp_to_string e1
                   ^ ") (" ^ exp_to_string e2 ^ ")"

(***** Expression denotation *)

// Use a map that stores for each variable
// (1) its denotation that should be treated abstractly (type a) and
// (2) user-specified extra information depending on its term (type b)

let vmap (a b:Type) = list (var * (a*b)) * (a * b)
let const (#a #b:Type) (xa:a) (xb:b) : vmap a b = [], (xa,xb)
let select (#a #b:Type) (x:var) (vm:vmap a b) : Tot a =
  match assoc #var #(a * b) x (fst vm) with
  | Some (a, _) -> a
  | _ -> fst (snd vm)
let select_extra (#a #b:Type) (x:var) (vm:vmap a b) : Tot b =
  match assoc #var #(a * b) x (fst vm) with
  | Some (_, b) -> b
  | _ -> snd (snd vm)
let update (#a #b:Type) (x:var) (xa:a) (xb:b) (vm:vmap a b) : vmap a b =
  (x, (xa, xb))::fst vm, snd vm

let rec mdenote (#a #b:Type) (m:cm a) (vm:vmap a b) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Var x -> select x vm
  | Mult e1 e2 -> CM?.mult m (mdenote m vm e1) (mdenote m vm e2)

let rec xsdenote (#a #b:Type) (m:cm a) (vm:vmap a b) (xs:list var) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select x vm
  | x::xs' -> CM?.mult m (select x vm) (xsdenote m vm xs')

(***** Flattening expressions to lists of variables *)

let rec flatten (e:exp) : list var =
  match e with
  | Unit -> []
  | Var x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

let rec flatten_correct_aux (#a #b:Type) (m:cm a) (vm:vmap a b)
                                                  (xs1 xs2:list var) :
    Lemma (xsdenote m vm (xs1 @ xs2) == CM?.mult m (xsdenote m vm xs1)
                                                   (xsdenote m vm xs2)) =
  match xs1 with
  | [] -> CM?.left_unitality m (xsdenote m vm xs2)
  | [x] -> if (Nil? xs2) then CM?.right_unitality m (select x vm)
  | x::xs1' -> (CM?.associativity m (select x vm)
                      (xsdenote m vm xs1') (xsdenote m vm xs2);
                flatten_correct_aux m vm xs1' xs2)

let rec flatten_correct (#a #b:Type) (m:cm a) (vm:vmap a b) (e:exp) :
    Lemma (mdenote m vm e == xsdenote m vm (flatten e)) =
  match e with
  | Unit | Var _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m vm (flatten e1) (flatten e2);
                  flatten_correct m vm e1; flatten_correct m vm e2

(***** Permuting the lists of variables
       by swapping adjacent elements *)

(* The user has control over the permutation. He can store extra
   information in the vmap and use that for choosing the
   permutation. This means that permute has access to the vmap. *)

let permute (b:Type) = a:Type -> vmap a b -> list var -> list var

// high-level correctness criterion for permutations
let permute_correct (#b:Type) (p:permute b) =
  #a:Type -> m:cm a -> vm:vmap a b -> xs:list var ->
    Lemma (xsdenote m vm xs == xsdenote m vm (p a vm xs))

// sufficient condition:
// permutation has to be expressible as swaps of adjacent list elements

let swap (n:nat) :Type = x:nat{x < n-1}

let rec apply_swap_aux (#a:Type) (n:nat) (xs:list a) (s:swap (length xs + n)) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases xs) =
  match xs with
  | [] | [_] -> xs
  | x1 :: x2 :: xs' -> if n = (s <: nat)
                       then x2 :: x1 :: xs'
                       else x1 :: apply_swap_aux (n+1) (x2 :: xs') s

let apply_swap (#a:Type) = apply_swap_aux #a 0

let rec apply_swap_aux_correct (#a #b:Type) (n:nat) (m:cm a) (vm:vmap a b)
                           (xs:list var) (s:swap (length xs + n)) :
    Lemma (requires True)
      (ensures (xsdenote m vm xs == xsdenote m vm (apply_swap_aux n xs s)))
      (decreases xs) =
  match xs with
  | [] | [_] -> ()
  | x1 :: x2 :: xs' ->
      if n = (s <: nat)
      then (// x1 + (x2 + xs') =a (x1 + x2) + xs'
            //                 =c (x2 + x1) + xs' = a x2 + (x1 + xs')
           let a = CM?.associativity m in
           a (select x1 vm) (select x2 vm) (xsdenote m vm xs');
           a (select x2 vm) (select x1 vm) (xsdenote m vm xs');
           CM?.commutativity m (select x1 vm) (select x2 vm))
      else apply_swap_aux_correct (n+1) m vm (x2 :: xs') s

let apply_swap_correct (#a #b:Type) (m:cm a) (vm:vmap a b)
                           (xs:list var) (s:swap (length xs)):
    Lemma (requires True)
          (ensures (xsdenote m vm xs == xsdenote m vm (apply_swap xs s)))
          (decreases xs) = apply_swap_aux_correct 0 m vm xs s

let rec apply_swaps (#a:Type) (xs:list a) (ss:list (swap (length xs))) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases ss) =
  match ss with
  | [] -> xs
  | s::ss' -> apply_swaps (apply_swap xs s) ss'

let rec apply_swaps_correct (#a #b:Type) (m:cm a) (vm:vmap a b)
                            (xs:list var) (ss:list (swap (length xs))):
    Lemma (requires True)
      (ensures (xsdenote m vm xs == xsdenote m vm (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> ()
  | s::ss' -> apply_swap_correct m vm xs s;
              apply_swaps_correct m vm (apply_swap xs s) ss'

let permute_via_swaps (#b:Type) (p:permute b) =
  (#a:Type) -> (vm:vmap a b) -> xs:list var ->
    Lemma (exists ss. p a vm xs == apply_swaps xs ss)

let rec permute_via_swaps_correct_aux
  (#b:Type) (p:permute b) (pvs:permute_via_swaps p)
  (#a:Type) (m:cm a) (vm:vmap a b)  (xs:list var) :
    Lemma (xsdenote m vm xs == xsdenote m vm (p a vm xs)) =
  pvs vm xs;
  assert(exists ss. p a vm xs == apply_swaps xs ss);
  exists_elim (xsdenote m vm xs == xsdenote m vm (p a vm xs))
    (() <: squash (exists ss. p a vm xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct m vm xs ss)

let permute_via_swaps_correct
  (#b:Type) (p:permute b) (pvs:permute_via_swaps p) : permute_correct p =
     permute_via_swaps_correct_aux p pvs

// TODO In the general case, an arbitrary permutation can be done via
// swaps. To show this we could for instance, write the permutation as
// a sequence of transpositions and then each transposition as a
// series of swaps.

(***** Sorting variables is a correct permutation
       (since it can be done by swaps) *)

// Here we sort without associating any extra information with the
// variables and only look at the actual identifiers

let sort : permute unit =
  (fun a vm -> List.Tot.sortWith #nat (compare_of_bool (<)))

// TODO: Show that sorting is a correct way to permute things;
// from sortWith_permutation we get
// (ensures (forall x. count x l = count x (sortWith f l)))
// but need instead a sequence of swaps of adjacent elements
// - can probably use bubble sort to show this special case

let rec bubble_sort_with_aux1 (#a:Type) (f:(a -> a -> Tot int)) (xs:list a) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length xs == length zs))
                  (decreases (length xs)) =
  match xs with
  | [] | [_] -> xs
  | x1 :: x2 :: xs' ->
      if f x1 x2 > 0 then x2 :: bubble_sort_with_aux1 f (x1::xs')
                     else x1 :: bubble_sort_with_aux1 f (x2::xs')

let rec bubble_sort_with_aux2 (#a:Type) (n:nat) (f:(a -> a -> Tot int))
          (xs:(list a){n <= length xs}) : Tot (list a)
              (decreases (length xs - n <: nat)) =
  if n = length xs then xs
  else bubble_sort_with_aux2 (n+1) f (bubble_sort_with_aux1 f xs)

let bubble_sort_with (#a:Type) = bubble_sort_with_aux2 #a 0

let sort_via_swaps (#a:Type) (vm : vmap a unit)  (xs:list var) :
  Lemma (exists ss. sort a vm xs == apply_swaps xs ss) = admit() // TODO

let rec sort_correct_aux (#a:Type) (m:cm a) (vm:vmap a unit) (xs:list var) :
    Lemma (xsdenote m vm xs == xsdenote m vm (sort a vm xs)) =
  permute_via_swaps_correct #unit sort (fun #a vm -> sort_via_swaps vm) m vm xs

let sort_correct : permute_correct #unit sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

let canon (#a #b:Type) (vm:vmap a b) (p:permute b) (e:exp) = p a vm (flatten e)

let canon_correct (#a #b:Type) (p:permute b) (pc:permute_correct p)
                       (m:cm a) (vm:vmap a b) (e:exp) :
    Lemma (mdenote m vm e == xsdenote m vm (canon vm p e)) =
  flatten_correct m vm e; pc m vm (flatten e)

let monoid_reflect (#a #b:Type) (p:permute b) (pc:permute_correct p)
                   (m:cm a) (vm:vmap a b) (e1 e2:exp)
    (_ : squash (xsdenote m vm (canon vm p e1) ==
                 xsdenote m vm (canon vm p e2)))
    : squash (mdenote m vm e1 == mdenote m vm e2) =
  canon_correct p pc m vm e1; canon_correct p pc m vm e2

(* Finds the position of first occurrence of x in xs;
   TODO: move this to the standard library, just where?  Is there any
         way I can add a new list function to the libraries without
         giving separate realizations in OCaml and F*? *)
let rec where_aux (#a:eqtype) (n:nat) (x:a) (xs:list a) :
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if x = x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
#reset-options "--z3rlimit 30"
let rec reification_aux (#a #b:Type) (ts:list term) (vm:vmap a b) (f:term->Tac b)
    (mult unit t : term) : Tac (exp * list term * vmap a b) =
  let hd, tl = collect_app_ref t in
  let tl = list_unref tl in
  let fvar (t:term) (ts:list term) (vm:vmap a b) : Tac (exp * list term * vmap a b) =
    match where t ts with
    | Some v -> (Var v, ts, vm)
    | None -> let vfresh = length ts in let z = unquote t in
              (Var vfresh, ts @ [t], update vfresh z (f t) vm)
  in
  match inspect hd, tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1,ts,vm) = reification_aux ts vm f mult unit t1 in
          let (e2,ts,vm) = reification_aux ts vm f mult unit t2 in
          (Mult e1 e2, ts, vm))
    else fvar t ts vm
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, vm)
    else fvar t ts vm
#reset-options "--z3rlimit 5"

// TODO: could guarantee same-length lists
let reification (b:Type) (f:term->Tac b) (def:b) (#a:Type) (m:cm a) (ts:list term) :
    Tac (list exp * vmap a b) =
  let mult = norm_term [delta] (quote (CM?.mult m)) in
  let unit = norm_term [delta] (quote (CM?.unit m)) in
  let ts   = Tactics.Derived.map (norm_term [delta]) ts in
  // dump ("mult = " ^ term_to_string mult ^
  //     "; unit = " ^ term_to_string unit ^
  //     ";  t   = " ^ term_to_string t);
  let (es,_, vm) =
    Tactics.Derived.fold_left
      (fun (es,vs,vm) t ->
        let (e,vs,vm) = reification_aux vs vm f mult unit t in (e::es,vs,vm))
      ([],[], const (CM?.unit m) def) ts
  in (List.rev es,vm)

let canon_monoid_with
    (b:Type) (f:term->Tac b) (def:b) (p:permute b) (pc:permute_correct p)
    (#a:Type) (m:cm a) : Tac unit =
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) t1 t2 ->
      // dump ("t1 =" ^ term_to_string t1 ^
      //     "; t2 =" ^ term_to_string t2);
      if term_eq t (quote a) then
        match reification b f def m [t1;t2] with
        | [r1;r2], vm ->
          // dump ("r1=" ^ exp_to_string r1 ^
          //     "; r2=" ^ exp_to_string r2);
          // dump ("vm =" ^ term_to_string (quote vm));
          change_sq (quote (mdenote m vm r1 == mdenote m vm r2));
          // dump ("before =" ^ term_to_string (norm_term [delta;primops]
          //   (quote (mdenote m vm r1 == mdenote m vm r2))));
          // dump ("expected after =" ^ term_to_string (norm_term [delta;primops]
          //   (quote (xsdenote m vm (canon vm p r1) ==
          //           xsdenote m vm (canon vm p r2)))));
          apply (quote (monoid_reflect #a #b p pc));
          // dump ("after apply");
          unfold_def (quote p);
          // dump ("after unfold");
          norm [delta_only [// term_to_string (quote p);
                            "CanonCommMonoid.canon";
                            "CanonCommMonoid.xsdenote";
                            "CanonCommMonoid.flatten";
                            "CanonCommMonoid.select";
                            "CanonCommMonoid.select_extra";
                            "FStar.List.Tot.Base.assoc";
                            "FStar.Pervasives.Native.fst";
                            "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
                            "FStar.List.Tot.Base.op_At";
                            "FStar.List.Tot.Base.append";
            (* TODO: the rest is a super brittle stop-gap, know thy instances *)
                            "FStar.List.Tot.Base.sortWith";
                            "FStar.List.Tot.Base.partition";
                            "FStar.List.Tot.Base.bool_of_compare";
                            "FStar.List.Tot.Base.compare_of_bool";
                            "CanonCommMonoid.const_compare";
                            "CanonCommMonoid.special_compare";
             ]; primops] // TODO: restrict primops to "less than" only
          // ; dump "done"
        | _ -> fail "Unexpected"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"

let canon_monoid = canon_monoid_with unit (fun _ -> ()) ()
                                     sort (fun #a -> sort_correct #a)

(***** Examples *)

let lem0 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid int_plus_cm; trefl())

(* Trying to enable computation with constants beyond unit.
   It might be enough to move all them to the end of the list by
   a careful ordering and let the normalizer do its thing: *)

// remember if something is a constant or not
let is_const (t:term) : Tac bool = Tv_Const? (inspect t)

// sort things and put the constants last
let const_compare (#a:Type) (vm:vmap a bool) (x y:var) =
  match select_extra x vm, select_extra y vm with
  | false, false | true, true -> compare_of_bool (<) x y
  | false, true -> 1
  | true, false -> -1

let const_last (a:Type) (vm:vmap a bool) (xs:list var) : list var =
  List.Tot.sortWith #nat (const_compare vm) xs

let canon_monoid_const = canon_monoid_with bool is_const false
  const_last (fun #a m vm xs -> admit())
(* TODO Try to reduce the number of admits by further generalizing
        the sort stuff at the top (from `unit` to `a`). *)

let lem1 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid_const int_plus_cm; trefl())

(* Trying to only bring some constants to the front,
   as Nik said would be useful for separation logic *)

// remember if something is a constant or not
let is_special (ts:list term) (t:term) : Tac bool = t `mem` ts

// put the special things sorted before the non-special ones,
// but don't change anything else
let special_compare (#a:Type) (vm:vmap a bool) (x y:var) =
  match select_extra x vm, select_extra y vm with
  | false, false -> 0
  | true, true -> compare_of_bool (<) x y
  | false, true -> -1
  | true, false -> 1

let special_first (a:Type) (vm:vmap a bool) (xs:list var) : list var =
  List.Tot.sortWith #nat (special_compare vm) xs

let canon_monoid_special (ts:list term) =
  canon_monoid_with bool (is_special ts) false special_first
                    (fun #a m vm xs -> admit())

let lem2 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid_special [quote a; quote b] int_plus_cm;
            dump "this won't work, admitting"; admit1())

(* Trying to do something separation logic like. Want to
   prove a goal of the form: given some concrete h0 and h1
   exists h1', h1 * h1' == h0. -- can use apply exists_intro to get an uvar
   Do this for an arbitrary commutative monoid. *)

let sep_logic
// TODO: this generality makes unfold_def fail with:
//       (Error) Variable "mult#1139342" not found
//       - Guido thinks this is related to
//         https://github.com/FStarLang/FStar/issues/1392
// (a:Type) (m:cm a) (x y z1 z2 z3 : a) = let op_Star = CM?.mult m in
// so working around it for now
(x y z1 z2 z3 : int) = let m = int_multiply_cm in let op_Star = op_Multiply in
  let h0 = z1 * CM?.unit m * (x * z2 * y * CM?.unit m) * z3 in
  let h1 = x * y in
  assert_by_tactic (exists h1'. h1 * h1' == h0)
  (fun _ -> apply_lemma (`exists_intro);
            flip();
            canon_monoid m;
            trefl();
            // this one blows up big time (takes up all RAM)
            // exact (cur_witness())
            dismiss()
  )

(* TODO: Need better control of reduction:
         - unfold_def still not good enough, see stopgap above *)

(* TODO: need a version of canon that works on assumption(s)
         (canon_in / canon_all) *)

(* TODO: Wondering whether we should support arbitrary re-association?
         Could be useful for separation logic, but we might also just
         work around it. *)

(* TODO: would be nice to just find all terms of monoid type in the
         goal and replace them with their canonicalization;
         basically use flatten_correct instead of monoid_reflect
         - for this to be efficient need Nik's pointwise' that can
           stop traversing when finding something interesting
         - even better, the user would have control over the place(s)
           where the canonicalization is done *)

(* TODO (open ended) Do the things used for reflective tactics really
                     need to be this pure? Can we prove correctness of
                     denotations intrinsically / by monadic
                     reification for an effectful denotation? *)

(* Old discussion discuss with Nik and Guido about spurious SMT obligations:
Nik:
- it's easy to get rid of some of the hasEq goals by just saying `let
  var :eqtype = nat`
- but, we still have some extra SMT goals
- and this is because reification computes a vmap literal vm, which
  computes all the way to a lambda term
  `(fun x -> if x = a then (a, ()) else ... )`
- and we have to prove that this thing is actually a vmap
- i wonder if there's some way for reification to compute this without
  fully normalizing it down to a lambda term, i.e., can we leave it as
  an `update (const_map ...) x a (a, ())` etc.
- if so, then proving it is a vmap will be trivial and will not incur
  additional SMT goals
- this reminds me a little of many prior conversations, including our
  conversation at the pub yesterday, Catalin. i.e., we want to treat
  `update` etc. abstractly in some places, but in other places, we
  want to compute fully with it (edited)
- I think we should be able to do that with our tactics
- e.g., something like `let r = set_norm_flags "don't unfold update,
  const"; let r = reification m [t1;t2] in reset_norm_flags; r in ...`
- for some as yet unavailable `set_norm_flags` tactic
- anyway, it's a detail, but one that I suspect we'll have to solve
  well especially as we build large vmap literals
*)
