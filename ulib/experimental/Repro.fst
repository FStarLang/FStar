module Repro
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
val h_admit (#a:Type) (#[@resolve_framing] p:hprop) (q:a -> hprop) : SteelT a p q

let split_frame outer inner = frame:hprop {can_be_split_into outer inner frame}

#push-options "--admit_smt_queries true"
let solve_split_frame (outer:hprop) : Tot (split_frame outer emp) = outer
#pop-options

assume
val my_frame_t
  (outer:hprop)
  (#[@resolve_framing] frame:split_frame outer emp)
  (_:unit)
  : SteelT unit outer (fun _ -> frame)

open FStar.Tactics
module T = FStar.Tactics

[@(resolve_implicits)
  (resolve_framing)]
let resolve () : Tac unit =
  let rec aux (i:int) : Tac unit =
//    T.dump ("State: " ^ string_of_int i);
    match T.goals () with
    | [] -> ()
    | g :: _ ->
      let f = T.term_as_formula' (goal_type g) in
//      T.print ("Goal formula is " ^ (formula_to_string f));
      match f with
      | Comp (Eq _) _ _ ->
//        T.print "Solving equality goal\n";
        T.trefl();
        aux (i + 1)

      | _ -> //has to be framing
        T.print "Solving framing goal\n";
        T.apply (`solve_split_frame);
        aux (i + 1)
  in
  aux 0


//succeeds if you open SteelT.Effect instead of Steel.Effect
//#push-options "--debug Repro --debug_level ResolveImplicitsHook"

val test_ok1 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok1 _
  = let tr = dependent_provides () in
    let c = my_frame_t (myref_hprop tr) (*#(myref_hprop tr)*) () in
    h_admit #unit (*(myref_hprop tr)*) (fun _ -> emp)


assume
val frame_t_emp
  (#[@resolve_framing] outer:hprop)
  (#[@resolve_framing] inner:hprop)
  (#[@resolve_framing] frame:split_frame outer inner)
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
  (#[@resolve_framing] outer:hprop)
  (#[@resolve_framing] inner0:hprop)
  (#[@resolve_framing] inner1:hprop)
  (#[@resolve_framing] frame:split_frame outer inner0)
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
             (#[@resolve_framing] p:hprop)
             (#[@resolve_framing] q:a -> hprop)
             (_:unit) : SteelT a p q

val test_ok4 (_:unit)
  : SteelT unit emp (fun c -> emp)
let test_ok4 _
  = let tr = dependent_provides () in
    let c = frame_t nop in
    h_admit' ()
