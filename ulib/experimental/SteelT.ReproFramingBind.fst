module SteelT.ReproFramingBind
open Steel.Memory.Tactics
open Steel.Memory
open SteelT.FramingBind

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
val h_admit (#a:Type)
             (#[@resolve_framing] p:hprop)
             (#[@resolve_framing] q:a -> hprop)
             (_:unit) : SteelT a p q

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
    // T.dump ("State: " ^ string_of_int i);
    match T.goals () with
    | [] -> ()
    | g :: _ ->
      let f = T.term_as_formula' (goal_type g) in
      // T.print ("Goal formula is " ^ (formula_to_string f));
      match f with
      | Comp (Eq _) _ _ ->
        // T.print "Solving equality goal\n";
        T.trefl();
        aux (i + 1)

      | _ -> //has to be framing
        // T.print "Solving framing goal\n";
        T.focus resolve_frame;
        aux (i + 1)
  in
  aux 0


assume
val ret (#a:_) 
        (#[@resolve_framing] p:a -> hprop)
        (x:a)
        (#[@resolve_framing] q: hprop)
        (#[@resolve_framing] _u:squash (can_be_split_into q (p x) emp))
        (_:unit)
        : SteelT a q p

val test_ok2 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok2 _
  = let tr = dependent_provides () in
    let c = nop () in
    h_admit ()

val test_ok3 (_:unit)
  : SteelT myref emp myref_hprop
let test_ok3 _
  = let tr = dependent_provides () in
    let _ = nop () in
    ret tr ()


val test_ok4 (_:unit)
  : SteelT myref emp myref_hprop
let test_ok4 _
  = let tr = dependent_provides () in
    ret tr (nop ())
