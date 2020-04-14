module Tick

open FStar.Seq

(* 'a is Type _ *)
val id : 'a -> 'a
let id x = x

val fst : 'a & 'b -> 'a
let fst (x, y) = x

(* Never worked: Identifier not found 'a *)
let fst' (p : 'a & 'b) = fun (x, _) -> x
let fst'' (p : 'a & 'b) = match p with (x, _) -> x

(* This does *)
let id' (x : 'a) = x

(* 'a is Type_, 'l1 and 'l2 are nat *)
val concat_lseq : lseq 'a 'l1 -> lseq 'a 'l2 -> lseq 'a ('l1 + 'l2)
let concat_lseq s1 s2 = append s1 s2

let concat_lseq' (s1 : lseq 'a 'l1) (s2 : lseq 'a 'l2) : lseq 'a ('l1 + 'l2) = append s1 s2

(* Can't infer the type of 'a, which makes sense. *)
(* This was previously working (!!!) by making 'a:Type *)
[@(expect_failure [66])]
val _lem : unit -> Lemma ('a == 'a)

(* Same thing *)
[@(expect_failure [66])]
val _lem2 : #a:_ -> unit -> Lemma (a == a)

(* This fails since `'typ` comes after the `'a`, `'b` and `'c` variables
(we sort them by name), and hence the type of `'a` cannot depend on it.
If it were first, which can be done by renaming, then it works fine.
See the examples below. *)
[@@expect_failure [54]]
val lem : unit -> Lemma (List.Tot.rev #'typ ['a; 'b; 'c] == ['c; 'b; 'a])
let lem () = ()

(* Works fine explicitly *)
val lemexp : #typ:_ -> #a:_ -> #b:_ -> #c:_ ->
             unit -> Lemma (List.Tot.rev #typ [a; b; c] == [c; b; a])
let lemexp () = ()

(* And also if we trick the sorting *)
val lemtrick : unit -> Lemma (List.Tot.rev #'typ ['xa; 'xb; 'xc] == ['xc; 'xb; 'xa])
let lemtrick () = ()
