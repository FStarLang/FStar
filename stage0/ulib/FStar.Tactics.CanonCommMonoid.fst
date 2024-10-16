(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Tactics.CanonCommMonoid

open FStar.Algebra.CommMonoid
open FStar.List
open FStar.Reflection.V2
open FStar.Tactics.V2
open FStar.Classical
open FStar.Tactics.CanonCommSwaps

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(* An expression canonizer for commutative monoids.
   Inspired by:
   - http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html
   - http://poleiro.info/posts/2015-04-13-writing-reflective-tactics.html
*)

(* Only dump when debugging is on *)
private let dump m = if debugging () then dump m

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

let vmap (a b:Type) = list (var & (a&b)) & (a & b)
let const (#a #b:Type) (xa:a) (xb:b) : vmap a b = [], (xa,xb)
let select (#a #b:Type) (x:var) (vm:vmap a b) : Tot a =
  match assoc #var #(a & b) x (fst vm) with
  | Some (a, _) -> a
  | _ -> fst (snd vm)
let select_extra (#a #b:Type) (x:var) (vm:vmap a b) : Tot b =
  match assoc #var #(a & b) x (fst vm) with
  | Some (_, b) -> b
  | _ -> snd (snd vm)
let update (#a #b:Type) (x:var) (xa:a) (xb:b) (vm:vmap a b) : vmap a b =
  (x, (xa, xb))::fst vm, snd vm

let rec mdenote (#a #b:Type) (m:cm a) (vm:vmap a b) (e:exp) : Tot a =
  match e with
  | Unit -> CM?.unit m
  | Var x -> select x vm
  | Mult e1 e2 -> CM?.mult m (mdenote m vm e1) (mdenote m vm e2)

let rec xsdenote (#a #b:Type) (m:cm a) (vm:vmap a b) (xs:list var) : Tot a =
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
  | [] -> CM?.identity m (xsdenote m vm xs2)
  | [x] -> if (Nil? xs2) then right_identity m (select x vm)
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

let permute_via_swaps_correct_aux
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

(***** Sorting variables is a correct permutation
       (since it can be done by swaps) *)

// Here we sort without associating any extra information with the
// variables and only look at the actual identifiers

let sort : permute unit =
  (fun a vm -> List.Tot.Base.sortWith #nat (compare_of_bool (<)))

let sortWith (#b:Type) (f:nat -> nat -> int) : permute b =
  (fun a vm -> List.Tot.Base.sortWith #nat f)

let sort_via_swaps (#a:Type) (vm : vmap a unit) (xs:list var) :
    Lemma (exists ss. sort a vm xs == apply_swaps xs ss) =
  List.Tot.Properties.sortWith_permutation #nat (compare_of_bool (<)) xs;
  let ss = equal_counts_implies_swaps #nat xs (sort a vm xs) in
  assert (sort a vm xs == apply_swaps xs ss)

let sortWith_via_swaps (#a #b:Type) (f:nat -> nat -> int)
    (vm : vmap a b) (xs:list var) :
    Lemma (exists ss. sortWith #b f a vm xs == apply_swaps xs ss) =
  List.Tot.Properties.sortWith_permutation #nat f xs;
  let ss = equal_counts_implies_swaps #nat xs (sortWith #b f a vm xs) in
  assert (sortWith #b f a vm xs == apply_swaps xs ss)

let sort_correct_aux (#a:Type) (m:cm a) (vm:vmap a unit) (xs:list var) :
    Lemma (xsdenote m vm xs == xsdenote m vm (sort a vm xs)) =
  permute_via_swaps_correct #unit sort sort_via_swaps m vm xs

let sortWith_correct_aux (#a #b:Type) (f:nat -> nat -> int) (m:cm a) (vm:vmap a b) (xs:list var) :
    Lemma (xsdenote m vm xs == xsdenote m vm (sortWith #b f a vm xs)) =
  permute_via_swaps_correct (sortWith f) (fun #a -> sortWith_via_swaps f) m vm xs

let sort_correct : permute_correct #unit sort = sort_correct_aux

let sortWith_correct (#b:Type) (f:nat -> nat -> int) :
  permute_correct #b (sortWith #b f) =
  (fun #a -> sortWith_correct_aux #a #b f)

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

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq_old x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (#a #b:Type) (unquotea:term->Tac a) (ts:list term)
    (vm:vmap a b) (f:term->Tac b)
    (mult unit t : term) : Tac (exp & list term & vmap a b) =
  let hd, tl = collect_app_ref t in
  let fvar (t:term) (ts:list term) (vm:vmap a b) : Tac (exp & list term & vmap a b) =
    match where t ts with
    | Some v -> (Var v, ts, vm)
    | None -> let vfresh = length ts in let z = unquotea t in
              (Var vfresh, ts @ [t], update vfresh z (f t) vm)
  in
  match inspect hd, list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq_old (pack (Tv_FVar fv)) mult
    then (let (e1,ts,vm) = reification_aux unquotea ts vm f mult unit t1 in
          let (e2,ts,vm) = reification_aux unquotea ts vm f mult unit t2 in
          (Mult e1 e2, ts, vm))
    else fvar t ts vm
  | _, _ ->
    if term_eq_old t unit
    then (Unit, ts, vm)
    else fvar t ts vm

// TODO: could guarantee same-length lists
let reification (b:Type) (f:term->Tac b) (def:b) (#a:Type)
    (unquotea:term->Tac a) (quotea:a -> Tac term) (tmult tunit:term) (munit:a)
    (ts:list term) :
    Tac (list exp & vmap a b) =
  let tmult: term = norm_term [delta;zeta;iota] tmult in
  let tunit: term = norm_term [delta;zeta;iota] tunit in
  let ts   = Tactics.Util.map (norm_term [delta;zeta;iota]) ts in
  // dump ("mult = " ^ term_to_string mult ^
  //     "; unit = " ^ term_to_string unit ^
  //     ";  t   = " ^ term_to_string t);
  let (es,_, vm) =
    Tactics.Util.fold_left
      (fun (es,vs,vm) t ->
        let (e,vs,vm) = reification_aux unquotea vs vm f tmult tunit t
        in (e::es,vs,vm))
      ([],[], const munit def) ts
  in (List.Tot.Base.rev es,vm)

val term_mem: term -> list term -> Tac bool
let rec term_mem x = function
  | [] -> false
  | hd::tl -> if term_eq_old hd x then true else term_mem x tl

let unfold_topdown (ts: list term) =
  let should_rewrite (s:term) : Tac (bool & int) =
    (term_mem s ts, 0)
  in
  let rewrite () : Tac unit =
    norm [delta];
    trefl()
  in
  topdown_rewrite should_rewrite rewrite

let rec quote_list (#a:Type) (ta:term) (quotea:a->Tac term) (xs:list a) :
    Tac term =
  match xs with
  | [] -> mk_app (`Nil) [(ta, Q_Implicit)]
  | x::xs' -> mk_app (`Cons) [(ta, Q_Implicit);
                              (quotea x, Q_Explicit);
                              (quote_list ta quotea xs', Q_Explicit)]

let quote_vm (#a #b:Type) (ta tb: term)
    (quotea:a->Tac term) (quoteb:b->Tac term) (vm:vmap a b) : Tac term =
  let quote_pair (p:a&b) : Tac term =
    mk_app (`Mktuple2) [(ta, Q_Implicit); (tb, Q_Implicit);
           (quotea (fst p), Q_Explicit); (quoteb (snd p), Q_Explicit)] in
  let t_a_star_b = mk_e_app (`tuple2) [ta;tb] in
  let quote_map_entry (p:(nat&(a&b))) : Tac term =
    mk_app (`Mktuple2) [(`nat, Q_Implicit); (t_a_star_b, Q_Implicit);
      (pack (Tv_Const (C_Int (fst p))), Q_Explicit);
      (quote_pair (snd p), Q_Explicit)] in
  let tyentry = mk_e_app (`tuple2) [(`nat); t_a_star_b] in
  let tlist = quote_list tyentry quote_map_entry (fst vm) in
  (* dump (term_to_string (tc tlist)); *)
  let tpair = quote_pair (snd vm) in
  (* dump (term_to_string (tc tpair)); *)
  let tylist = mk_e_app (`list) [tyentry] in
  (* dump (term_to_string (tc tylist)); *)
  mk_app (`Mktuple2) [(tylist, Q_Implicit); (t_a_star_b, Q_Implicit);
                      (tlist, Q_Explicit); (tpair, Q_Explicit)]

let rec quote_exp (e:exp) : Tac term =
  match e with
  | Unit -> `Unit
  | Var x -> mk_e_app (`Var) [pack (Tv_Const (C_Int x))]
  | Mult e1 e2 -> mk_e_app (`Mult) [quote_exp e1; quote_exp e2]

(* [@@plugin] *)
let canon_monoid_aux
    (a b: Type) (ta: term) (unquotea: term -> Tac a) (quotea: a -> Tac term)
    (tm tmult tunit: term) (munit: a) (tb: term) (quoteb:b->Tac term)
    (f:term->Tac b) (def:b) (tp:term) (tpc:term): Tac unit =
  norm [];
  match term_as_formula (cur_goal ()) with
  | Comp (Eq (Some t)) t1 t2 ->
      // dump ("t1 =" ^ term_to_string t1 ^
      //     "; t2 =" ^ term_to_string t2);
      if term_eq_old t ta then
        match reification b f def unquotea quotea tmult tunit munit [t1;t2] with
        | [r1;r2], vm ->
          // dump ("r1=" ^ exp_to_string r1 ^
          //     "; r2=" ^ exp_to_string r2);
          // dump ("vm =" ^ term_to_string (quote vm));

          // change_sq (quote (mdenote m vm r1 == mdenote m vm r2));
          // TODO: quasi-quotes would help at least for splicing in the vm r1 r2
          let tvm = quote_vm ta tb quotea quoteb vm in
          let tr1 = quote_exp r1 in
          let tr2 = quote_exp r2 in
          let teq:term = mk_app (`eq2)
            [(ta,                                                      Q_Implicit);
             (mk_app (`mdenote) [(ta,Q_Implicit); (tb,Q_Implicit);
                 (tm,Q_Explicit); (tvm,Q_Explicit); (tr1,Q_Explicit)], Q_Explicit);
             (mk_app (`mdenote) [(ta,Q_Implicit); (tb,Q_Implicit);
                 (tm,Q_Explicit); (tvm,Q_Explicit); (tr2,Q_Explicit)], Q_Explicit)] in
          change_sq teq;

          // dump ("before =" ^ term_to_string (norm_term [delta;primops]
          //   (quote (mdenote m vm r1 == mdenote m vm r2))));
          // dump ("expected after =" ^ term_to_string (norm_term [delta;primops]
          //   (quote (xsdenote m vm (canon vm p r1) ==
          //           xsdenote m vm (canon vm p r2)))));
          // mapply0 (quote (monoid_reflect #a #b p pc));
          mapply0 (mk_app (`monoid_reflect) [(ta, Q_Implicit);
                                            (tb, Q_Implicit);
                                            (tp, Q_Explicit);
                                            (tpc, Q_Explicit)]);
          (* dump ("before unfold, tp = " ^ term_to_string tp); *)
          unfold_topdown [(`canon); (`xsdenote); tp];
          (* dump ("after unfold"); *)
          // would like to do only this norm [primops] but ...
          // for now having to do all this mess
          norm [delta_only [// term_to_string tp;
                            `%canon;
                            `%xsdenote;
                            `%flatten;
                            `%select;
                            `%select_extra;
                            `%quote_list;
                            `%quote_vm;
                            `%quote_exp;

                            (* Defined ahead *)
                            "FStar.Tactics.CanonCommMonoid.const_compare";
                            "FStar.Tactics.CanonCommMonoid.special_compare";

                            `%FStar.Pervasives.Native.fst;
                            `%FStar.Pervasives.Native.snd;
                            `%FStar.Pervasives.Native.__proj__Mktuple2__item___1;
                            `%FStar.Pervasives.Native.__proj__Mktuple2__item___2;

                            `%FStar.List.Tot.assoc;
                            `%FStar.List.Tot.op_At;
                            `%FStar.List.Tot.append;

            (* TODO: the rest is a super brittle stop-gap, know thy instances *)
                            "SL.AutoTactic.compare_b";
                            "SL.AutoTactic.compare_v";
                            `%FStar.Order.int_of_order;
                            `%FStar.Reflection.V2.compare_term;
                            `%FStar.List.Tot.sortWith;
                            `%FStar.List.Tot.partition;
                            `%FStar.List.Tot.bool_of_compare;
                            `%FStar.List.Tot.compare_of_bool;
             ]; zeta; iota; primops] // TODO: restrict primops to "less than" only
                         // - would need this even if unfold_def did it's job?
          // ; dump "done"
        | _ -> fail "Unexpected"
      else fail "Goal should be an equality at the right monoid type"
  | _ -> fail "Goal should be an equality"

let canon_monoid_with
    (b:Type) (f:term->Tac b) (def:b) (p:permute b) (pc:permute_correct p)
    (#a:Type) (m:cm a) : Tac unit =
  canon_monoid_aux a b
    (quote a) (unquote #a) (fun (x:a) -> quote x)
    (quote m) (quote (CM?.mult m)) (quote (CM?.unit m)) (CM?.unit m)
    (quote b) (fun (x:b) -> quote x) f def (quote p) (quote (pc <: permute_correct p))

let canon_monoid (#a:Type) (cm:cm a) : Tac unit =
  canon_monoid_with unit (fun _ -> ()) ()
    (fun a -> sort a) sort_correct cm

(***** Examples *)

let lem0 (a b c d : int) =
  assert (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  by (canon_monoid int_plus_cm; trefl ())


// (* Trying to enable computation with constants beyond unit.
//    It might be enough to move all them to the end of the list by
//    a careful ordering and let the normalizer do its thing: *)

// remember if something is a constant or not
let is_const (t:term) : Tac bool = Tv_Const? (inspect t)

// sort things and put the constants last
let const_compare (#a:Type) (vm:vmap a bool) (x y:var) =
  match select_extra x vm, select_extra y vm with
  | false, false | true, true -> compare_of_bool (<) x y
  | false, true -> 1
  | true, false -> -1

let const_last (a:Type) (vm:vmap a bool) (xs:list var) : list var =
  List.Tot.Base.sortWith #nat (const_compare vm) xs

let canon_monoid_const #a cm = canon_monoid_with bool is_const false
  (fun a -> const_last a)
  (fun #a m vm xs -> sortWith_correct #bool (const_compare vm) #a m vm xs) #a cm

let lem1 (a b c d : int) =
  assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1)
  (fun _ -> canon_monoid_const int_plus_cm; trefl())

// (* Trying to only bring some constants to the front,
//    as Nik said would be useful for separation logic *)

// remember if something is a constant or not
let is_special (ts:list term) (t:term) : Tac bool = t `term_mem` ts

// put the special things sorted before the non-special ones,
// but don't change anything else
let special_compare (#a:Type) (vm:vmap a bool) (x y:var) =
  match select_extra x vm, select_extra y vm with
  | false, false -> 0
  | true, true -> compare_of_bool (<) x y
  | false, true -> -1
  | true, false -> 1

let special_first (a:Type) (vm:vmap a bool) (xs:list var) : list var =
  List.Tot.Base.sortWith #nat (special_compare vm) xs

let special_first_correct : permute_correct special_first =
    (fun #a m vm xs -> sortWith_correct #bool (special_compare vm) #a m vm xs)

let canon_monoid_special (ts:list term) =
  canon_monoid_with bool (is_special ts) false
    (fun a -> special_first a)
    special_first_correct
