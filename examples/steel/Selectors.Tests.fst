module Selectors.Tests

open Steel.Memory
open Steel.SelectorEffect

open FStar.Tactics

let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    slterm_nbr_uvars hd + fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args
  | Tv_Abs _ t -> slterm_nbr_uvars t
  // TODO: Probably need to check that...
  | _ -> 0

let rec filter_goals (l:list goal) : Tac (list goal) =
  match l with
  | [] -> []
  | hd::tl ->
      match term_as_formula' (goal_type hd) with
      | Comp (Eq _) _ _ -> hd::filter_goals tl
      | App t _ -> if term_eq t (`squash) then hd::filter_goals tl else filter_goals tl
      | _ -> filter_goals tl

let rec solve_next (l:list goal) : Tac bool =
  match l with
  | [] -> false
  | hd::tl -> match term_as_formula' (goal_type hd) with
    | Comp (Eq _) l r ->
      let lnbr = slterm_nbr_uvars l in
      let rnbr = slterm_nbr_uvars r in
      if lnbr = 0 || rnbr = 0 then (focus trefl; true) else (later(); solve_next tl)
    | App _ t -> begin
      match term_as_formula' t with
      | Comp (Eq _) l r ->
      let lnbr = slterm_nbr_uvars l in
      let rnbr = slterm_nbr_uvars r in
      if lnbr = 0 || rnbr = 0 then (focus trefl; true) else (later(); solve_next tl)
      | _ -> false
      end
    | _ -> fail "test"; false


let rec resolve_sel_rec () : Tac unit =
  if solve_next (goals()) then resolve_sel_rec()

[@@ resolve_implicits; framing_implicit_sel]
let resolve_sel () : Tac unit =
  let gs = filter_goals (goals()) in
  set_goals gs;
  dump "all goals";
  resolve_sel_rec ()

assume val ref : Type0
assume val ptr (_:ref) : hprop u#1
assume val sel (r:ref) : projection int (ptr r)

let vemp' : viewable =
  { fp = emp;
    a = unit;
    sel = fun _ -> () }

let vptr' (r:ref) : viewable =
  { fp = ptr r;
    a = int;
    sel = sel r }

let vemp : viewables = VUnit vemp'
let vptr (r:ref) : viewables = VUnit (vptr' r)

assume val alloc (x:int) : Steel_Sel ref vemp (fun r -> vptr r)
  (fun _ -> True) (fun _ r h1 ->  h1 (vptr r) == x)
assume val free (r:ref) : Steel_Sel unit (vptr r) (fun _ -> vemp) (fun _ -> True) (fun _ _ _ -> True)
assume val read (r:ref) : Steel_Sel int (vptr r) (fun _ -> vptr r)
  (fun _ -> True)
  (fun h0 x h1 -> h0 == h1 /\ x == h1 (vptr r))

assume val ret (#a:Type) (x:a) (p:a -> viewables)
  : Steel_Sel a (p x) p (fun _ -> True) (fun _ _ _ -> True)

assume val h_assert (pre:viewables) (req:req_t pre) :
  Steel_Sel unit pre (fun _ -> pre)
    (fun _ -> True) // wrong
    (fun _ _ h1 -> req h1)

assume val h_admit (#a:Type)
  (#[@@framing_implicit_sel] pre:viewables) (#[@@framing_implicit_sel] post:post_t a)
  (#ens:ens_t pre a post) (_:unit) : Steel_Sel a pre post (fun _ -> True) ens

let test1 (x:int) : Steel_Sel ref vemp vptr (fun _ -> True) (fun _ _ _ -> True) =
  //(fun _ r h1 -> h1 (vptr r) == x) =
  let y = alloc x in
  h_assert (vptr y) (fun _ -> True);
  ret y vptr
