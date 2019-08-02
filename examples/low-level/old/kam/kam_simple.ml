(**
 * Cf.
 *     An abstract machine for Lambda-terms normalization
 *     P. Cregut
 *     Proceedings of the 1990 ACM conference on LISP and functional programming
 *     http://dl.acm.org/citation.cfm?doid=91556.91681&CFID=723138393&CFTOKEN=40299162
 **)

(**
  * $ make kam_simple.exe
  * $ ./kam_simple
  *   (Abs a (Abs b b))  (after using about 4GB and 20 secs)
  **)

type tm =
  | Var of int          (* de Bruijn *)
  | Name of int
  | Abs of tm
  | App of tm  * tm

type env = closure list

and closure =
  | Open of int
  | Clos of env * tm

type stack = closure list

let rec find env x = match env with
  | k::tl ->
    if x=0 then k else find tl (x - 1)
  | [] -> raise Not_found

let rec norm (env:env) (stack:stack) (tm:tm) (n:int) : tm = match tm with
  | Abs body ->
    begin match stack with
          | [] ->
             let m = n + 1 in
             Abs (norm (Open m :: env) stack body m)
          | hd::tl ->
             norm (hd::env) tl body n
    end

  | App(t1, t2) ->
     norm env (Clos (env, t2)::stack) t1 n

  | Var x ->
    let k = find env x in
    begin match k with
      | Open m ->
        rebuild env (Var (n - m)) stack n

      | Clos(env', tm) ->
        norm env' stack tm n
    end

  | Name _ -> failwith "OPEN TERM"

and rebuild env head stack n = match stack with
  | [] -> head
  | hd::tl ->
     let arg = match hd with
       | Open m -> Var (n - m)
       | Clos (env, tm) -> norm env [] tm n in
     rebuild env (App(head, arg)) tl n

let norm e = norm [] [] e 0

(**********************************)
(* PRINTING TERMS *)
(**********************************)
let push m =
  let next_char = fst m + 1 in
  let x = Char.chr next_char in
  x, (next_char, x::snd m)

let rec term_to_string_raw = function
  | Var x -> string_of_int x
  | Name x -> Printf.sprintf "(Name %d)" x
  | Abs tm -> Printf.sprintf  "(Abs %s)" (term_to_string_raw tm)
  | App(t1, t2) -> Printf.sprintf "(App %s %s)" (term_to_string_raw t1) (term_to_string_raw t2)

let rec clos_to_string = function
  | Open m -> Printf.sprintf "(Open %d)" m
  | Clos(env, x) -> Printf.sprintf "(Clos %s %s)" (env_to_string env) (term_to_string_raw x)

and env_to_string env =
  let s = List.map clos_to_string env in
  Printf.sprintf "[%s]" (String.concat "; " s)

let print_term_raw t = print_string (term_to_string_raw t)

let rec print_term m = function
  | Var x -> print_char (find (snd m) x)
  | Name x -> print_string "(Name "; print_int x; print_string ")"
  | Abs tm -> let x, m = push m in print_string "(Abs "; print_char x; print_string " "; print_term m tm; print_string ")"
  | App(t1, t2) -> print_string "("; print_term m t1; print_string " "; print_term m t2; print_string ")"

let print_term = print_term (Char.code 'a' - 1, [])

(*********************************)
(* SOME UTILITIES TO BUILD TERMS *)
(*********************************)
let rec close x ix body = match body with
  | Var _ -> body
  | Name y -> if y=x then Var ix else body
  | App(t1, t2) -> App(close x ix t1, close x ix t2)
  | Abs t -> Abs (close x (ix + 1) t)
let abs (x, body) = Abs (close x 0 body)

let x = 0
let y = 1
let f = 2
let g = 3
let n = 4
let h = 5
let m = 6

(* Church numerals *)
let z = abs(f, abs(x, Name x))
let one = abs(f, abs(x, App(Name f, Name x)))
let succ n = abs(f, abs(x, App(Name f, App(App(n, Name f), Name x))))
let pred = abs(n, abs(f, abs(x, App(App(App(Name n, (abs(g, abs(h, App(Name h, App(Name g, Name f)))))), abs(y, Name x)), abs(y, Name y)))))
let minus m n = App(App(n, pred), m)
let mul = abs(m, abs(n, abs(f, App(Name m, (App(Name n, Name f))))))
let let_ x e e' = App (abs(x, e'), e)

let rec encode (n:int) =
  if n = 0 then z
  else succ (encode (n - 1))

(*****************************************)
(* Testing it by running 10,000 - 10,000 *)
(*****************************************)
let test_it =
(*  let ten = encode 10 in
  let hundred = App(App(mul, ten), ten) in
  let k = App(App(mul, ten), hundred) in
  let ten_k = App(App(mul, ten), k) in
*)
  let n = encode 5000 in
  let let_bound_name = 100 in
  let x =
    let_ let_bound_name
         n
         (minus (Name let_bound_name)
                (Name let_bound_name)) in
  print_string "\n";
  print_term (norm x);
  print_string "\n"
