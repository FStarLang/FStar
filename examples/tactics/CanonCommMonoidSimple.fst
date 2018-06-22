module CanonCommMonoidSimple

open FStar.Algebra.CommMonoid
open FStar.List
open FStar.Tactics
open FStar.Reflection
open FStar.Classical

(* A simple expression canonizer for commutative monoids.
   For a canonizer with more features see CanonCommMonoid.fst.

   Inspired by:
   - http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html
   - http://poleiro.info/posts/2015-04-13-writing-reflective-tactics.html
*)

(***** Expression syntax *)

let var : eqtype = nat

type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Var : var -> exp

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

let vmap (a:Type) = list (var * a) * a
let const (#a:Type) (xa:a) : vmap a = ([], xa)
let select (#a:Type) (x:var) (vm:vmap a) : Tot a =
  match assoc #var #a x (fst vm) with
  | Some a -> a
  | _ -> snd vm
let update (#a:Type) (x:var) (xa:a) (vm:vmap a) : vmap a =
  (x, xa)::fst vm, snd vm

let rec mdenote (#a:Type) (m:cm a) (vm:vmap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Var x -> select x vm
  | Mult e1 e2 -> CM?.mult m (mdenote m vm e1) (mdenote m vm e2)

let rec xsdenote (#a:Type) (m:cm a) (vm:vmap a) (xs:list var) : a =
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

let rec flatten_correct_aux (#a:Type) (m:cm a) (vm:vmap a) (xs1 xs2:list var) :
    Lemma (xsdenote m vm (xs1 @ xs2) == CM?.mult m (xsdenote m vm xs1)
                                                   (xsdenote m vm xs2)) =
  match xs1 with
  | [] -> CM?.identity m (xsdenote m vm xs2)
  | [x] -> if (Nil? xs2) then right_identity m (select x vm)
  | x::xs1' -> (CM?.associativity m (select x vm)
                      (xsdenote m vm xs1') (xsdenote m vm xs2);
                flatten_correct_aux m vm xs1' xs2)

let rec flatten_correct (#a:Type) (m:cm a) (vm:vmap a) (e:exp) :
    Lemma (mdenote m vm e == xsdenote m vm (flatten e)) =
  match e with
  | Unit | Var _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m vm (flatten e1) (flatten e2);
                  flatten_correct m vm e1; flatten_correct m vm e2

(***** Permuting the lists of variables
       by swapping adjacent elements *)

let permute = list var -> list var

// high-level correctness criterion for permutations
let permute_correct (p:permute) =
  #a:Type -> m:cm a -> vm:vmap a -> xs:list var ->
    Lemma (xsdenote m vm xs == xsdenote m vm (p xs))

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

let rec apply_swap_aux_correct (#a:Type) (n:nat) (m:cm a) (vm:vmap a)
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

let apply_swap_correct (#a:Type) (m:cm a) (vm:vmap a)
                       (xs:list var) (s:swap (length xs)):
    Lemma (ensures (xsdenote m vm xs == xsdenote m vm (apply_swap xs s)))
          (decreases xs) = apply_swap_aux_correct 0 m vm xs s

let rec apply_swaps (#a:Type) (xs:list a) (ss:list (swap (length xs))) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases ss) =
  match ss with
  | [] -> xs
  | s::ss' -> apply_swaps (apply_swap xs s) ss'

let rec apply_swaps_correct (#a:Type) (m:cm a) (vm:vmap a)
                            (xs:list var) (ss:list (swap (length xs))):
    Lemma (requires True)
      (ensures (xsdenote m vm xs == xsdenote m vm (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> ()
  | s::ss' -> apply_swap_correct m vm xs s;
              apply_swaps_correct m vm (apply_swap xs s) ss'

let permute_via_swaps (p:permute) =
  (#a:Type) -> (vm:vmap a) -> xs:list var ->
    Lemma (exists ss. p xs == apply_swaps xs ss)

let rec permute_via_swaps_correct_aux (p:permute) (pvs:permute_via_swaps p)
                               (#a:Type) (m:cm a) (vm:vmap a) (xs:list var) :
    Lemma (xsdenote m vm xs == xsdenote m vm (p xs)) =
  pvs vm xs;
  assert(exists ss. p xs == apply_swaps xs ss);
  exists_elim (xsdenote m vm xs == xsdenote m vm (p xs))
    (() <: squash (exists ss. p xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct m vm xs ss)

let permute_via_swaps_correct
  (p:permute) (pvs:permute_via_swaps p) : permute_correct p =
     fun #a -> permute_via_swaps_correct_aux p pvs #a

// TODO In the general case, an arbitrary permutation can be done via
// swaps. To show this we could for instance, write the permutation as
// a sequence of transpositions and then each transposition as a
// series of swaps.

(***** Sorting variables is a correct permutation
       (since it can be done by swaps) *)

// Here we sort the variable numbers

let sort : permute = List.Tot.sortWith #nat (compare_of_bool (<))

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

let sort_via_swaps (#a:Type) (vm : vmap a)  (xs:list var) :
  Lemma (exists ss. sort xs == apply_swaps xs ss) = admit() // TODO

let rec sort_correct_aux (#a:Type) (m:cm a) (vm:vmap a) (xs:list var) :
    Lemma (xsdenote m vm xs == xsdenote m vm (sort xs)) =
  permute_via_swaps_correct sort (fun #a vm -> sort_via_swaps vm) m vm xs

let sort_correct : permute_correct sort = (fun #a -> sort_correct_aux #a)

(***** Canonicalization tactics *)

[@plugin]
let canon (e:exp) = sort (flatten e)

let canon_correct (#a:Type) (m:cm a) (vm:vmap a) (e:exp) :
    Lemma (mdenote m vm e == xsdenote m vm (canon e)) =
  flatten_correct m vm e; sort_correct m vm (flatten e)

let monoid_reflect_orig (#a:Type) (m:cm a) (vm:vmap a) (e1 e2:exp) :
  Lemma (requires (xsdenote m vm (canon e1) == xsdenote m vm (canon e2)))
        (ensures (mdenote m vm e1 == mdenote m vm e2)) =
  canon_correct m vm e1; canon_correct m vm e2

let monoid_reflect (#a:Type) (m:cm a) (vm:vmap a) (e1 e2:exp)
    (_ : squash (xsdenote m vm (canon e1) == xsdenote m vm (canon e2)))
       : squash (mdenote m vm e1 == mdenote m vm e2) =
  canon_correct m vm e1; canon_correct m vm e2

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (#a:Type) (ts:list term) (vm:vmap a)
                        (mult unit t : term) : Tac (exp * list term * vmap a) =
  let hd, tl = collect_app_ref t in
  let fvar (t:term) (ts:list term) (vm:vmap a) : Tac (exp * list term * vmap a) =
    match where t ts with
    | Some v -> (Var v, ts, vm)
    | None -> let vfresh = length ts in let z = unquote t in
              (Var vfresh, ts @ [t], update vfresh z vm)
  in
  match inspect hd, list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1,ts,vm) = reification_aux ts vm mult unit t1 in
          let (e2,ts,vm) = reification_aux ts vm mult unit t2 in
          (Mult e1 e2, ts, vm))
    else fvar t ts vm
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, vm)
    else fvar t ts vm

let reification (#a:Type) (m:cm a) (ts:list term) (vm:vmap a) (t:term) :
    Tac (exp * list term * vmap a) =
  let mult = norm_term [delta] (quote (CM?.mult m)) in
  let unit = norm_term [delta] (quote (CM?.unit m)) in
  let t    = norm_term [delta] t in
  reification_aux ts vm mult unit t

let canon_monoid (#a:Type) (m:cm a) : Tac unit =
  norm [];
  match term_as_formula (cur_goal ()) with
  | Comp (Eq (Some t)) t1 t2 ->
      // dump ("t1 =" ^ term_to_string t1 ^
      //     "; t2 =" ^ term_to_string t2);
      if term_eq t (quote a) then
        let (r1, ts, vm) = reification m [] (const (CM?.unit m)) t1 in
        let (r2, _, vm) = reification m ts vm t2 in
        // dump ("vm =" ^ term_to_string (quote vm));
        change_sq (quote (mdenote m vm r1 == mdenote m vm r2));
        // dump ("before =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (mdenote m vm r1 == mdenote m vm r2))));
        // dump ("expected after =" ^ term_to_string (norm_term [delta;primops]
        //   (quote (xsdenote m vm (canon r1) ==
        //           xsdenote m vm (canon r2)))));
        apply (`monoid_reflect);
        // dump ("after apply");
        norm [delta_only [`%canon; `%xsdenote; `%flatten; `%sort;
                `%select; `%assoc; `%fst; `%__proj__Mktuple2__item___1;
                `%(@); `%append; `%List.Tot.Base.sortWith;
                `%List.Tot.Base.partition; `%bool_of_compare; `%compare_of_bool;
           ]; primops]
        // ;dump "done"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"

(***** Example *)

let lem0 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid int_plus_cm; trefl())

open FStar.Mul

let _ =
  assert_by_tactic (forall (a b c d : int). (b * 1) * 2 * a * (c * a) * 1 == 1 * a * b * c * a * 2)
  (fun _ -> ignore (forall_intros()); canon_monoid int_multiply_cm; trefl())
