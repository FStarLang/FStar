module NewCanon

open FStar.Tactics


let rec get_candidates (t:term) (l:list term) : Tac (list term) =
  let name, _ = collect_app t in
  match l with
  | [] -> []
  | hd::tl ->
      let n, _ = collect_app hd in
      if term_eq n name then (
        hd::(get_candidates t tl)
      ) else get_candidates t tl


let rec trivial_cancel (t:term) (l:list term) =
  match l with
  | [] -> false, l
  | hd::tl ->
      if term_eq hd t then
        // These elements match, we remove them
        true, tl
      else (let b, res = trivial_cancel t tl in b, hd::res)

let rec trivial_cancels (l1 l2:list term) : Tac (list term * list term) =
  match l1 with
  | [] -> [], l2
  | hd::tl ->
      let b, l2'   = trivial_cancel  hd l2 in
      let l1', l2' = trivial_cancels tl l2' in
      (if b then l1' else hd::l1'), l2'

assume val p (#n:int) (n2:int) : Type
assume val q (#n:int) (n2:int) : Type

let rec dump_terms (l:list term) : Tac unit =
  match l with
  | [] -> dump "end"; ()
  | hd::tl -> dump (term_to_string hd); dump_terms tl

let rec try_candidates (t:term) (l:list term) : Tac (term * int) =
  match l with
  | [] -> t, 0
  | hd::tl ->
      let res = unify t hd in
      let t', n' = try_candidates t tl in
      if res then hd, 1 + n'  else t', n'

let rec remove_from_list (t:term) (l:list term) : Tac (list term) =
  match l with
  | [] -> fail "should not happen"; []
  | hd::tl ->
      if unify t hd then tl else hd::remove_from_list t tl

let rec equivalent_lists' (l1 l2:list term) : Tac unit =
  match l1 with
  | [] -> begin match l2 with
    | [] -> dump "equiv"
    | _ -> dump "not equiv"
    end
  | hd::tl ->
    let t, n = try_candidates hd l2 in
    if n = 0 then
      fail ("no candidate found for scrutinee " ^ term_to_string hd)
    else if n = 1 then (
      let l2 = remove_from_list t l2 in
      equivalent_lists' tl l2
    ) else
      fail "too many candidates"

let equivalent_lists (l1 l2:list term) : Tac unit =
  let l1, l2 = trivial_cancels l1 l2 in
  equivalent_lists' l1 l2

#set-options "--print_implicits"

let _ =
  let terms:list term = [(`p #0 1); (`p #1 0); (`q #1 1)] in
  let p_terms:list term = [(`p #_ 0); (`p #0 1); (`q #1 1)] in
  let t1:term = `p #0 1 in
  // let t2:term = `p #_ 0 in
//  assert (True) by (dump_terms terms);
  assert (True) by (
    // let n = try_candidates t1 [t2] in
    // dump (string_of_int n));
    equivalent_lists terms p_terms);
//    equivalent_lists [t] (filter_on_head t terms));
  ()
