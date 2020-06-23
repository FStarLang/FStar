module NewCanon

open FStar.Tactics

(* For a given term t, collect all terms in the list l with the same head symbol *)
let rec get_candidates (t:term) (l:list term) : Tac (list term) =
  let name, _ = collect_app t in
  match l with
  | [] -> []
  | hd::tl ->
      let n, _ = collect_app hd in
      if term_eq n name then (
        hd::(get_candidates t tl)
      ) else get_candidates t tl

(* Try to remove a term that is exactly matching, not just that can be unified *)
let rec trivial_cancel (t:term) (l:list term) =
  match l with
  | [] -> false, l
  | hd::tl ->
      if term_eq hd t then
        // These elements match, we remove them
        true, tl
      else (let b, res = trivial_cancel t tl in b, hd::res)

(* Call trivial_cancel on all elements of l1 *)
let rec trivial_cancels (l1 l2:list term) : Tac (list term * list term) =
  match l1 with
  | [] -> [], l2
  | hd::tl ->
      let b, l2'   = trivial_cancel  hd l2 in
      let l1', l2' = trivial_cancels tl l2' in
      (if b then l1' else hd::l1'), l2'

let rec dump_terms (l:list term) : Tac unit =
  match l with
  | [] -> dump "end"; ()
  | hd::tl -> dump (term_to_string hd); dump_terms tl

(* For a list of candidates l, count the number that can unify with t *)
let rec try_candidates (t:term) (l:list term) : Tac (term * int) =
  match l with
  | [] -> t, 0
  | hd::tl ->
      let res = unify t hd in
      let t', n' = try_candidates t tl in
      if res then hd, 1 + n'  else t', n'

(* Remove one term from the list if it can unify. Only to be called when
   try_candidates succeeded *)
let rec remove_from_list (t:term) (l:list term) : Tac (list term) =
  match l with
  | [] -> fail "should not happen"; []
  | hd::tl ->
      if unify t hd then tl else hd::remove_from_list t tl

(* Check if two lists of slprops are equivalent by recursively calling
   try_candidates.
   Assumes that only l2 contains terms with the head symbol unresolved.
   It returns all elements that were not resolved during this iteration *)
let rec equivalent_lists_once (l1 l2:list term) : Tac (list term * list term) =
  match l1 with
  | [] -> [], l2
  | hd::tl ->
    let t, n = try_candidates hd l2 in
    if n = 0 then
      fail ("not equiv: no candidate found for scrutinee " ^ term_to_string hd)
    else if n = 1 then (
      let l2 = remove_from_list t l2 in
      equivalent_lists_once tl l2
    ) else
      // Too many candidates for this scrutinee
      let rem1, rem2 = equivalent_lists_once tl l2 in
      hd::rem1, rem2

(* Recursively calls equivalent_lists_once.
   Stops when we're done with unification, or when we didn't make any progress
   If we didn't make any progress, we have too many candidates for some terms *)
let rec equivalent_lists' (n:nat) (l1 l2:list term) : Tac unit =
  match l1 with
  | [] -> begin match l2 with
    | [] -> dump "equiv"
    | _ ->
      // TODO: This should succeed if l2 only contains uvars or emp,
      //as it can be unified with emp
      dump "not equiv"
    end
  | _ ->
    let rem1, rem2 = equivalent_lists_once l1 l2 in
    let n' = List.Tot.length rem1 in
    if n' >= n then
      // Should always be smaller or equal to n
      fail ("too many candidates for scrutinee")
    else equivalent_lists' n' rem1 rem2

(* First remove all trivially equal terms, then try to decide equivalence *)
let equivalent_lists (l1 l2:list term) : Tac unit =
  let l1, l2 = trivial_cancels l1 l2 in
  let n = List.Tot.length l1 in
  equivalent_lists' n l1 l2

#set-options "--print_implicits"

assume val p (#n:int) (n2:int) : Type
assume val q (#n:int) (#n':int) (n2:int) : Type

let _ =
  let terms:list term =
//    [(`p #0 1); (`p #2 1); (`p #1 0); (`q #1 #2 1); (`q #_ #3 1)] in
    [(`p #0 1); (`p #2 1); (`p #1 0); (`q #_ #3 1); (`q #1 #2 1)] in
  let p_terms:list term =
    [(`p #2 1); (`p #_ 0); (`p #_ 1); (`q #_ #3 1); (`q #_ #_ 1)] in
  // The assertion fails because implicits are not unified in this case,
  // but the important part is the result of equivalent_lists, given as
  // a dump in the tactic.
  assert (True) by (
//    let u = fresh_uvar None in
    equivalent_lists terms p_terms);
  ()
