module Steel.Effects2.Tests

open Steel.Memory
open Steel.Effects2

open FStar.Tactics
open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics.CanonCommMonoidSimple.Equiv

// Does not form a monoid, but ok for now in our setting where sl_implies should be solved as equiv
inline_for_extraction noextract let req : equiv hprop =
  EQ sl_implies
     (fun _ -> admit())
     (fun _ _ -> admit())
     (fun _ _ _ -> admit())

inline_for_extraction noextract let rm : cm hprop req =
  CM emp
     star
     (fun _ -> admit())
     (fun _ _ _ -> admit())
     (fun _ _ -> admit())
     (fun _ _ -> admit())

inline_for_extraction noextract let canon () : Tac unit =
  canon_monoid (`req) (`rm)


let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    slterm_nbr_uvars hd + fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args
  | Tv_Abs _ t -> slterm_nbr_uvars t
  // TODO: Probably need to check that...
  | _ -> 0

let solve_can_be_split (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> norm [delta_only [`%can_be_split]];
                     canon ());
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let solve_can_be_split_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> ignore (forall_intro());
                     norm [delta_only [`%can_be_split_forall]];
                     norm [delta_only [
                            `%__proj__CM__item__unit;
                            `%__proj__CM__item__mult;
                            `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                            `%fst; `%snd];
                          primops; iota; zeta];
                     canon ());
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen


// Returns true if the goal has been solved, false if it should be delayed
let solve_or_delay (g:goal) : Tac bool =
  let f = term_as_formula' (goal_type g) in
  match f with
  | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (quote delay) then (focus (fun () -> dump "delay"); false)
      else if term_eq hd (quote can_be_split) then solve_can_be_split args
      else if term_eq hd (quote can_be_split_forall) then solve_can_be_split_forall args
      else false
  | Comp (Eq _) l r ->
    let lnbr = slterm_nbr_uvars l in
    let rnbr = slterm_nbr_uvars r in
    // Only solve equality if there is only one uvar
    if lnbr + rnbr <= 1 then (trefl (); true) else false
  | _ -> false


// Returns true if it successfully solved a goal
// If it returns false, it means it didn't find any solvable goal,
// which should mean only delayed goals are left
let rec pick_next (l:list goal) : Tac bool =
  match l with
  | [] -> false
  | a::q -> if solve_or_delay a then true else (later (); pick_next q)

[@@ resolve_implicits; framing_implicit]
let rec resolve_tac () : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    if pick_next g then resolve_tac ()
    else
      (norm [delta_only [`%delay]];
      resolve_tac ())


assume val ref : Type0
assume val ptr (_:ref) : hprop u#1

assume val alloc (x:int)  : SteelT ref emp ptr
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)

// #set-options "--debug Steel.Effects2.Tests --debug_level ResolveImplicitsHook --ugly // --print_implicits"
// #set-options "--debug Steel.Effects2.Tests --debug_level LayeredEffectsEqns --ugly // --debug_level ResolveImplicitsHook --print_implicits --debug_level Extreme // --debug_level Rel --debug_level TwoPhases"
// let test1 (x:int) : SteelT ref emp ptr = alloc x

// #set-options "--debug Steel.Effects2.Tests --debug_level Extreme --debug_level Rel --debug_level LayeredEffectsEqns --print_implicits --ugly --debug_level TwoPhases --print_bound_var_types"
let test2 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r) =
  let x = read r in
  steel_ret x
  //steel_ret x


// [@@expect_failure]
// let test2 (r1 r2:ref) : SteelT (int & int) (ptr r1 `star` ptr r2) (fun _ -> ptr r1 `star` ptr r2) =
//   let x = read r1 in
//   let y = read r2 in
//   steel_ret (x, y)
