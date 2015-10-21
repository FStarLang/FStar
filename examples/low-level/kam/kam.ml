let mk_list n =
  Camlstack.push_frame ();
  let out = Camlstack.mkref [] in
  for i = 0 to n do
    out := Camlstack.cons i !out;
  done;
  Camlstack.pop_frame()

;; let _ = mk_list 1000

(**
 * Cf.
 *     An abstract machine for Lambda-terms normalization
 *     P. Cregut
 *     Proceedings of the 1990 ACM conference on LISP and functional programming  
 *     http://dl.acm.org/citation.cfm?doid=91556.91681&CFID=723138393&CFTOKEN=40299162
 **)

type tm =
  | Var of int
  | Abs of int * tm
  | App of tm  * tm 

type env = (int * closure) list
and closure = 
  | Clos of env * tm
  | Open

let null : closure = Obj.magic 0

type stack = tm list

let rec find env x : closure = match env with 
  | (y, k)::tl -> 
    if y=x then k else find tl x
  | [] -> raise Not_found

open Camlstack 
let rec norm (env:env) (stack:stack) (tm:tm) : tm = match tm with 
  | Abs(x, body) -> 
    begin match stack with 
      | [] -> Abs (x, norm (cons (mkpair x Open) env) stack body)
      | hd::tl -> norm (cons (mkpair x (Clos(env, hd))) env) tl body  (* How to alloc a Clos(env,hd) in a region? *)
    end

  | App(t1, t2) -> 
    norm env (cons t2 stack) t1

  | Var x -> 
    let k = find env x in
    match k with 
      | Open -> rebuild env tm stack
      | Clos(env', k) -> norm env' stack k

and rebuild env head stack = match stack with 
  | [] -> head
  | hd::tl -> rebuild env (App(head, norm env [] hd)) tl

let norm e = 
  push_frame();
  let x = norm [] [] e in 
  pop_frame(); 
  x

let _ = norm (Abs(0, App(Abs(1, Var 1), Var 0)))
