module IfcExampleReify2

open WhileReify
open IfcReify
open IfcTypechecker
open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.Exceptions

assume val hi : id
assume val lo : id
assume val c : id

let env var =
  if var = hi then Low
  else if var = lo then Low
    else if var = c then High
      else High

(*
  While c > 0{
    hi := lo + 1
    lo := hi + 1
    c := c - 1
  }
*)

let c_1 body = While (AVar c) body (AVar c)
let c_2 = Assign hi (AOp Plus (AVar lo) (AInt 1))
let c_3 = Assign lo (AOp Plus (AVar hi) (AInt 1))
let c_4 = Assign c (AOp Minus (AVar c) (AInt 1))
let c_body =  Seq (Seq c_2 c_3) c_4

let cmd = c_1 c_body

#set-options "--z3rlimit 30"
val c_2_3_ni : unit -> Lemma (ni_com env (Seq c_2 c_3) Low)
let c_2_3_ni () = ()


#set-options "--z3rlimit 5"
val cmd_ni : unit ->
  Exn label (requires True) (ensures fun ol -> Inl? ol ==> ni_com env cmd (Inl?.v ol))
let cmd_ni () =
  c_2_3_ni ();
  tc_com_hybrid env cmd [Seq c_2 c_3, Low]

val cmd_ni' : unit ->
  Exn label (requires True) (ensures fun ol -> Inl? ol ==> ni_com env cmd (Inl?.v ol))
  Lemma (ensures ni_com env cmd Low)
let cmd_ni' () =
  c_2_3_ni ();
  tc_com_hybrid env cmd [Seq c_2 c_3, Low]
  match reify (tc_com_hybrid env cmd [Seq c_2 c_3, Low]) with
  | Inl l -> ()

(*
./ifcExampleReify2.fst(45,2-46,15) : (Error) Expected type "(EXN_repr label (EXN_bind_wp ./ifcExampleReify2.fst(45,37-45,55) (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) label (EXN_lift_from_pure (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) (pure_bind_wp ./ifcExampleReify2.fst(45,37-45,55) (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) (pure_bind_wp ./ifcExampleReify2.fst(45,38-45,54) (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))}) (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) (pure_bind_wp ./ifcExampleReify2.fst(45,38-45,54) (tuple2 (?161923 uu___) (?161924 uu___)) (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))}) (pure_bind_wp ./ifcExampleReify2.fst(45,38-45,54) (tuple2 (?161923 uu___) (?161924 uu___)) (tuple2 (?161923 uu___) (?161924 uu___)) (pure_bind_wp ./ifcExampleReify2.fst(45,38-45,49) (?161923 uu___) (tuple2 (?161923 uu___) (?161924 uu___)) (pure_assert_p (?161923 uu___) (?161930 uu___ (Seq c_2 c_3)) (pure_return (?161923 uu___) (Seq c_2 c_3))) (fun _1 -> (pure_bind_wp ./ifcExampleReify2.fst(45,51-45,54) (?161924 uu___) (tuple2 (?161923 uu___) (?161924 uu___)) (pure_assert_p label (?161932 uu___ Low) (pure_return label Low)) (fun _2 -> (pure_null_wp (tuple2 (?161923 uu___) (?161924 uu___))))))) (fun uu___ -> (pure_assume_p (tuple2 (?161923 uu___) (?161924 uu___)) (eq2 uu___@0 (Mktuple2 (Seq c_2 c_3) Low)) (pure_return (tuple2 (?161923 uu___) (?161924 uu___)) uu___@0)))) (fun uu___ -> (pure_assert_p (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))}) (?161933 uu___ uu___@0) (pure_return (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))}) uu___@0)))) (fun hd -> (pure_null_wp (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))}))))) (fun uu___ -> (pure_assume_p (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) (eq2 uu___@0 (Cons (Mktuple2 (Seq c_2 c_3) Low) (Nil ))) (pure_return (list (cl#3417:(tuple2 com label){(ni_com env (fst cl@0) (snd cl@0))})) uu___@0))))) (fun uu___ -> (fun uu___ p -> (l_and l_True (l_Forall (fun r -> (l_imp (l_and l_True (l_imp (b2t (uu___is_Inl r@0)) (ni_com env cmd (__proj__Inl__item__v r@0)))) (p@1 r@0)))))))))";
got type "(either (?161991 uu___) (?161972 uu___))"
*)
