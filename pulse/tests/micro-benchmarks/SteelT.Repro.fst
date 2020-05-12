module SteelT.Repro
open Steel.Memory.Tactics
open Steel.Memory
open SteelT.Effect
//open Steel.Effect

assume
val myref : Type0

assume
val myref_hprop (x:myref) : hprop

assume
val dependent_provides (_:unit)
  : SteelT myref emp myref_hprop

assume
val nop (_:unit) : SteelT unit emp (fun c -> emp)

assume
val h_admit (#a:Type) (#[@@resolve_framing] p:hprop) (q:a -> hprop) : SteelT a p q

assume
val my_frame_t
  (outer:hprop)
  (#[@@resolve_framing] frame:hprop)
  (#[@@resolve_framing] _:squash (can_be_split_into outer emp frame))
  (_:unit)
  : SteelT unit outer (fun _ -> frame)

open FStar.Tactics
module T = FStar.Tactics

inline_for_extraction noextract let resolve_frame () : Tac unit =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_only [`%can_be_split_into]];
  norm [delta_attr [`%__reduce__];
        delta_only [
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta];
  canon()

[@(resolve_implicits)
  (resolve_framing)]
let resolve () : Tac unit =
    let rec aux (i:int) : Tac unit =
    T.dump ("State: " ^ string_of_int i);
    match T.goals () with
    | [] -> ()
    | g :: _ ->
      let f = T.term_as_formula' (goal_type g) in
      T.print ("Goal formula is " ^ (formula_to_string f));
      match f with
      | Comp (Eq _) _ _ ->
        T.print "Solving equality goal\n";
        T.trefl();
        aux (i + 1)

      | _ -> //has to be framing
        T.print "Solving framing goal\n";
        T.focus resolve_frame;
        aux (i + 1)
  in
  aux 0



//#push-options "--debug Repro --debug_level ResolveImplicitsHook"
#push-options "--print_implicits"
val test_ok1 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok1 _
  = let tr = dependent_provides () in
    let c = my_frame_t (myref_hprop tr) (*#(myref_hprop tr)*) () in
    h_admit #unit (*(myref_hprop tr)*) (fun _ -> emp)


assume
val frame_t_emp
  (#[@@resolve_framing] outer:hprop)
  (#[@@resolve_framing] inner:hprop)
  (#[@@resolve_framing] frame:hprop)
  (#[@@resolve_framing] _:squash (can_be_split_into outer inner frame))
  ($f:unit -> SteelT unit inner (fun _ -> emp))
  : SteelT unit outer (fun _ -> frame)


val test_ok2 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok2 _
  = let tr = dependent_provides () in
    let c = frame_t_emp nop in
    h_admit (fun _ -> emp)


assume
val frame_t
  (#[@@resolve_framing] outer:hprop)
  (#[@@resolve_framing] inner0:hprop)
  (#[@@resolve_framing] inner1:hprop)
  (#[@@resolve_framing] frame:hprop)
  (#[@@resolve_framing] _:squash (can_be_split_into outer inner0 frame))
  ($f:unit -> SteelT unit inner0 (fun _ -> inner1))
  : SteelT unit outer (fun _ -> frame `star` inner1)
val test_ok3 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok3 _
  = let tr = dependent_provides () in
    let c = frame_t nop in
    h_admit (fun _ -> emp)


assume
val h_admit' (#a:Type)
             (#[@@resolve_framing] p:hprop)
             (#[@@resolve_framing] q:a -> hprop)
             (_:unit) : SteelT a p q

val test_ok4 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok4 _
  = let tr = dependent_provides () in
    let c = frame_t nop in
    h_admit' ()
