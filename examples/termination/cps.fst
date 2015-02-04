(*************************************************************)
(*** A simple CPS function: adding the elements of a list. ***)
(*************************************************************)

(** First standard try: got a strange error message from F* **)
(* module SimpleCPS *)
(* open List *)

(* (\* *)
(* Expected a term of type "_9491:(int -> Tot (U377 'a l k hd tl)){(tl << l)}"; *)
(* got a function "(fun r -> (k (hd + r)))" (Annotated type is not a function) *)
(*  *\) *)
(* val add_cps : list int -> (int -> Tot 'a) -> Tot 'a *)
(* let rec add_cps l k = match l with *)
(*   | [] -> k 0 *)
(*   | hd::tl -> add_cps tl (fun (r:int) -> k (hd + r)) *)

(* val add : list int -> Tot int *)
(* let add l = add_cps l (fun x -> x) *)



(** Second try with λ-lifting: works well **)
module SimpleCPSLambdaLifting
open List

val add_cps_intern : (int -> Tot 'a) -> int -> int -> Tot 'a
let add_cps_intern k x y = k (x + y)

val add_cps : list int -> (int -> Tot 'a) -> Tot 'a
let rec add_cps l k = match l with
  | [] -> k 0
  | hd::tl -> add_cps tl (add_cps_intern k hd)

val add : list int -> Tot int
let add l = add_cps l (fun x -> x)



(** It is easy to defunctionalize it **)
module SimpleCPSDefun
open List

type cont =
  | C0 : cont
  | C1 : cont -> int -> cont

val apply : cont -> int -> Tot int
let rec apply k r = match k with
  | C0 -> r
  | C1 k hd -> apply k (hd + r)

val add_cps : list int -> cont -> Tot int
let rec add_cps l k = match l with
  | [] -> apply k 0
  | hd::tl -> add_cps tl (C1 k hd)

val add : list int -> Tot int
let add l = add_cps l C0



(*******************************************************************)
(*** A more complex CPS function: adding the elements of a tree. ***)
(*******************************************************************)

(** First standard try: got the same strange error message from F* as before **)
(* module DoubleCPS *)

(* type expr = *)
(*   | Const : int -> expr *)
(*   | Plus : expr -> expr -> expr *)

(* (\* *)
(* Expected a term of type "_11817:(int -> Tot (U404 'a e k e1 e2)){(e1 << e)}"; *)
(* got a function "(fun r1 -> (eval_cps e2 (fun r2 -> (k (r1 + r2)))))" (Annotated type is not a function) *)
(* *\) *)
(* val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a *)
(* let rec eval_cps e k = *)
(*   match e with *)
(*     | Const n -> k n *)
(*     | Plus e1 e2 -> eval_cps e1 (fun r1 -> eval_cps e2 (fun r2 -> k (r1 + r2))) *)



(** Second try with λ-lifting: involves a mutual recursion whose termination cannot be figured out by F* **)
(* module DoubleCPSLambdaLifting *)

(* type expr = *)
(*   | Const : int -> expr *)
(*   | Plus : expr -> expr -> expr *)

(* val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a *)
(* let eval_cps1 k r1 r2 = k (r1 + r2) *)

(* val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a *)
(* val eval_cps2 : expr -> (int -> Tot 'a) -> int -> Tot 'a *)

(* (\* *)
(*   Subtyping check failed; expected type _13024:(int -> Tot 'a){(%[e2] << %[e2; r1])}; got type (int -> Tot 'a) *)
(*  *\) *)
(* let rec eval_cps e k = *)
(*   match e with *)
(*     | Const n -> k n *)
(*     | Plus e1 e2 -> eval_cps e1 (eval_cps2 e2 k) *)

(* and eval_cps2 e2 k r1 = eval_cps e2 (eval_cps1 k r1) *)



(** Third try with greadier λ-lifting that removes mutual recursion: ok for F* **)
module DoubleCPSLambdaLifting2

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr

val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a
let eval_cps1 k r1 r2 = k (r1 + r2)

val eval_cps2 : (int -> Tot 'a) -> ((int -> Tot 'a) -> Tot 'a) -> int -> Tot 'a
let eval_cps2 k eval_cps r1 = eval_cps (eval_cps1 k r1)

val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a
let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (eval_cps2 k (eval_cps e2))

val eval : expr -> Tot int
let eval e = eval_cps e (fun x -> x)



(*******************************************************************************)
(*** Proving termination of its defunctionalized version is known to be hard ***)
(*******************************************************************************)

(** First standard try: as expected, F* cannot prove termination **)
(* module DoubleCPSDefun *)

(* type expr = *)
(*   | Const : int -> expr *)
(*   | Plus : expr -> expr -> expr *)

(* type cont = *)
(*   | C0 : cont *)
(*   | C1 : cont -> int -> cont *)
(*   | C2 : cont -> expr -> cont *)

(* val apply : cont -> int -> Tot int *)
(* val eval_cps : expr -> cont -> Tot int *)

(* let rec apply k r = match k with *)
(*     | C0 -> r *)
(*     | C1 k r1 -> apply k (r1 + r) *)
(*     | C2 k e2 -> eval_cps e2 (C1 k r) *)

(* and eval_cps e k = *)
(*   match e with *)
(*     | Const n -> apply k n *)
(*     | Plus e1 e2 -> eval_cps e1 (C2 k e2) *)



(** Second try with λ-lifting: I would not expect F* to be able to infer termination anyway, but actually I get another strange error message **)
(* module DoubleCPSDefunLambdaLifting *)

(* type expr = *)
(*   | Const : int -> expr *)
(*   | Plus : expr -> expr -> expr *)

(* type cont = *)
(*   | C0 : cont *)
(*   | C1 : cont -> int -> cont *)
(*   | C2 : cont -> expr -> cont *)

(* val apply : cont -> int -> (expr -> cont -> Tot int) -> Tot int *)
(* let rec apply k r eval_cps = match k with *)
(*     | C0 -> r *)
(*     | C1 k r1 -> apply k (r1 + r) eval_cps *)
(*     | C2 k e2 -> eval_cps e2 (C1 k r) *)

(* val eval_cps : expr -> cont -> Tot int *)
(* let rec eval_cps e k = *)
(*   match e with *)
(*     | Const n -> apply k n eval_cps *)
(*     | Plus e1 e2 -> eval_cps e1 (C2 k e2) *)
(* (\* *)
(*  Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error. *)
(* Bound term variable not found: _ *)
(* *\) *)
