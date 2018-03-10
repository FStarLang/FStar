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

(** *** Commutative monoids *)

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

(** *** Expression syntax *)

let var = nat
let var_ord : cmp var = (<=)
let vmap (a:Type) = ordmap var a var_ord
let select (#a:Type) (m:cm a) (x:var) (vars:vmap a) : a =
  match select x vars with
  | Some v -> v
  | None -> CM?.unit m // using monoid unit as a default for variables

type exp : Type =
  | Unit : exp
  | Var : var -> exp
  | Mult : exp -> exp -> exp

let rec exp_to_string (e:exp) =
  match e with
  | Unit -> "Unit"
  | Var x -> "Var " ^ string_of_int x
  | Mult e1 e2 -> "Mult (" ^ exp_to_string e1
                   ^ ") (" ^ exp_to_string e2 ^ ")"

let rec mdenote (#a:Type) (m:cm a) (vars:vmap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Var x -> select m x vars
  | Mult e1 e2 -> CM?.mult m (mdenote m vars e1) (mdenote m vars e2)

let rec xsdenote (#a:Type) (m:cm a) (vars:vmap a) (xs:list var) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select m x vars
  | x::xs' -> CM?.mult m (select m x vars) (xsdenote m vars xs')

let rec flatten (e:exp) : list var =
  match e with
  | Unit -> []
  | Var x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

let rec flatten_correct_aux (#a:Type) (m:cm a) (vars:vmap a) (xs1 xs2:list var) :
  Lemma (xsdenote m vars (xs1 @ xs2) == CM?.mult m (xsdenote m vars xs1)
                                                   (xsdenote m vars xs2)) =
  match xs1 with
  | [] -> CM?.left_unitality m (xsdenote m vars xs2)
  | [x] -> if (Nil? xs2) then CM?.right_unitality m (select m x vars)
  | x::xs1' -> (CM?.associativity m (select m x vars)
                      (xsdenote m vars xs1') (xsdenote m vars xs2);
                flatten_correct_aux m vars xs1' xs2)

let rec flatten_correct (#a:Type) (m:cm a) (vars:vmap a) (e:exp) :
    Lemma (mdenote m vars e == xsdenote m vars (flatten e)) =
  match e with
  | Unit | Var _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m vars (flatten e1) (flatten e2);
                  flatten_correct m vars e1; flatten_correct m vars e2

// TODO, from sortWith_permutation we get
// (ensures (forall x. count x l = count x (sortWith f l)))
// but need instead a sequence of swaps of adjacent elements
// (can probably use bubble sort to show that)
// and can use commutativity to justify each of these swaps

let sort = List.Tot.sortWith #nat (compare_of_bool (<))

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

let rec apply_swap_aux_correct (#a:Type) (n:nat) (m:cm a) (vars:vmap a)
                           (xs:list var) (s:swap (length xs + n)) :
    Lemma (requires True)
      (ensures (xsdenote m vars xs == xsdenote m vars (apply_swap_aux n xs s)))
      (decreases xs) =
  match xs with
  | [] | [_] -> ()
  | x1 :: x2 :: xs' ->
      if n = (s <: nat)
      then (// x1 + (x2 + xs') =a (x1 + x2) + xs'
            //                 =c (x2 + x1) + xs' = a x2 + (x1 + xs')
           let a = CM?.associativity m in
           a (select m x1 vars) (select m x2 vars) (xsdenote m vars xs');
           a (select m x2 vars) (select m x1 vars) (xsdenote m vars xs');
           CM?.commutativity m (select m x1 vars) (select m x2 vars))
      else apply_swap_aux_correct (n+1) m vars (x2 :: xs') s

let apply_swap_correct (#a:Type) (m:cm a) (vars:vmap a)
                           (xs:list var) (s:swap (length xs)):
    Lemma (requires True)
          (ensures (xsdenote m vars xs == xsdenote m vars (apply_swap xs s)))
          (decreases xs) = apply_swap_aux_correct 0 m vars xs s

let rec apply_swaps (#a:Type) (xs:list a) (ss:list (swap (length xs))) :
    Pure (list a) (requires True)
                  (ensures (fun zs -> length zs == length xs)) (decreases ss) =
  match ss with
  | [] -> xs
  | s::ss' -> apply_swaps (apply_swap xs s) ss'

let rec apply_swaps_correct (#a:Type) (m:cm a) (vars:vmap a)
                            (xs:list var) (ss:list (swap (length xs))):
    Lemma (requires True)
      (ensures (xsdenote m vars xs == xsdenote m vars (apply_swaps xs ss)))
      (decreases ss) =
  match ss with
  | [] -> ()
  | s::ss' -> apply_swap_correct m vars xs s;
              apply_swaps_correct m vars (apply_swap xs s) ss'

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

let permutation_via_swaps (#a:eqtype) (xs ys:list a) :
  Lemma (requires (forall x. count x xs = count x ys))
        // alternative pre-condition: ys == sort xs, wouldn't work for
        // permutations that are not sorting; but for that the proof
        // is different anyway (need something fancier than
        // bubble-sort for that)
        (ensures (exists ss. ys == apply_swaps xs ss)) = admit()

let rec sort_correct (#a:Type) (m:cm a) (vars:vmap a) (xs:list var) :
    Lemma (xsdenote m vars xs == xsdenote m vars (sort xs)) =
  sortWith_permutation (compare_of_bool (<)) xs;
  permutation_via_swaps xs (sort xs);
  assert(exists ss. sort xs == apply_swaps xs ss);
  exists_elim (xsdenote m vars xs == xsdenote m vars (sort xs))
    (() <: squash (exists ss. sort xs == apply_swaps xs ss))
    (fun ss -> apply_swaps_correct m vars xs ss)

let monoid_reflect (#a:Type) (m:cm a) (vars:vmap a) (e1 e2:exp)
    (_ : squash (xsdenote m vars (sort (flatten e1)) ==
                 xsdenote m vars (sort (flatten e2))))
    : squash (mdenote m vars e1 == mdenote m vars e2) =
  flatten_correct m vars e1; flatten_correct m vars e2;
  sort_correct m vars (flatten e1); sort_correct m vars (flatten e2)

(* Finds the position of first occurrence of x in xs;
   this could use eqtype and be completely standard if term provided it *)
let rec where_aux (n:nat) (x:term) (xs:list term) : Tot (option nat)
                                                        (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (#a:Type) (ts:list term) (vars:vmap a)
    (mult unit t : term) : Tac (exp * list term * vmap a) =
  let hd, tl = collect_app_ref t in
  let tl = list_unref tl in
  let fvar (t:term) (ts:list term) (vars:vmap a) : Tac (exp * list term * vmap a) =
    match where t ts with
    | Some v -> (Var v, ts, vars)
    | None -> let vfresh = length ts in let z = unquote t in
              (Var vfresh, ts @ [t], update vfresh z vars)
  in
  match inspect hd, tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1,ts,vars) = reification_aux ts vars mult unit t1 in
          let (e2,ts,vars) = reification_aux ts vars mult unit t2 in
          (Mult e1 e2, ts, vars))
    else fvar t ts vars
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, vars)
    else fvar t ts vars

// TODO: could guarantee same-length lists
let reification (#a:Type) (m:cm a) (ts:list term) : Tac (list exp * vmap a) =
    let mult = norm_term [delta] (quote (CM?.mult m)) in
    let unit = norm_term [delta] (quote (CM?.unit m)) in
    let ts   = Tactics.Derived.map (norm_term [delta]) ts in
    // dump ("mult = " ^ term_to_string mult ^
    //     "; unit = " ^ term_to_string unit ^
    //     ";  t   = " ^ term_to_string t);
    let (es,_, vars) =
      Tactics.Derived.fold_left
        (fun (es,vs,vars) t ->
          let (e,vs,vars) = reification_aux vs vars mult unit t in (e::es,vs,vars))
        ([],[],empty) ts
    in (List.rev es,vars)

private val conv : #x:Type0 -> #y:Type0 -> squash (y == x) -> x -> y
private let conv #x #y eq w = w

let change t1 =
    focus (fun () ->
        let g = cur_goal () in
        let t = mk_app (`conv) [(t1, Q_Implicit); (g,Q_Implicit)] in
        dump (term_to_string t1);
        apply t; // <- the problem is actually here
        dump "1";
        norm [delta;primops];
        dump "2";
        trivial ()
    )

let change_sq t1 =
    change (mk_e_app (`squash) [t1])

let canon_monoid (#a:Type) (m:cm a) : Tac unit =
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) t1 t2 ->
      dump ("t1 =" ^ term_to_string t1 ^
          "; t2 =" ^ term_to_string t2);
      if term_eq t (quote a) then
        match reification m [t1;t2] with
        | [r1;r2], vars ->
          dump ("r1=" ^ exp_to_string r1 ^
              "; r2=" ^ exp_to_string r2);
          dump ("vars =" ^ term_to_string (quote vars));
          dump ("before =" ^ term_to_string (norm_term [delta;primops]
            (quote (mdenote m vars r1 == mdenote m vars r2))));
          dump ("after =" ^ term_to_string (norm_term [delta;primops]
            (quote ((xsdenote m vars (sort (flatten r1)) ==
                     xsdenote m vars (sort (flatten r2)))))));
          change_sq (quote (mdenote m vars r1 == mdenote m vars r2));
          apply (`monoid_reflect);
          norm [delta_only ["CanonCommMonoid.xsdenote";
                            "CanonCommMonoid.flatten";
                            "FStar.List.Tot.Base.op_At";
                            "FStar.List.Tot.Base.append"]]; dump "done"
        | _ -> fail "Unexpected"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"

let lem0 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid int_plus_cm; trefl())

(* TODO: FStar.OrdMap abstraction was getting in the way of
         computation, find a cleaner way to remove it *)

(* TODO: Allow the tactic to compute with constants beyond unit.
         Would it be enough to move all them to the end of the list by
         a careful ordering and let the normalizer do its thing? *)

(* TODO: Allow the user control over the sorting ordering by allowing
         him to store extra information in the vmap and using that for
         the sorting. This would mean that sorting should have access
         to the vmap in the first place. *)

(* TODO: would be nice to just find all terms of monoid type in the
         goal and replace them with their canonicalization;
         basically use flatten_correct instead of monoid_reflect
         - for this to be efficient need Nik's pointwise' that can
           stop traversing when finding something interesting
         - even better, the user would have control over the place(s)
           where the canonicalization is done *)
