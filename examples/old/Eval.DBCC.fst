(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
////////////////////////////////////////////////////////////////////////////////
module Eval.DBCC

noeq type closure : Type -> Type -> Type =
  | Clos : env:Type -> #a:Type -> #b:Type -> x:env -> (y:env{y=x} -> a -> Tot b) -> closure a b

val apply: #a:Type -> #b:Type -> closure a b -> a -> Tot b
let apply #a #b (Clos 'env env f) a = f env a

noeq type var : Type -> Type -> Type =
   | O : g:Type -> a:Type -> var (g * a) a
   | S : g:Type -> a:Type -> b:Type -> var g a -> var (g * b) a

noeq type tm : Type -> Type -> Type =
  | Var : #g:Type -> #a:Type -> var g a -> tm g a
  | Lam : g:Type -> a:Type -> b:Type -> body:tm (g * a) b -> tm g (closure a b)
  | App : g:Type -> a:Type -> b:Type -> e1:tm g (closure a b) -> e2:tm g a -> tm g b

val eval_var: g:Type -> a:Type -> var g a -> g -> Tot a
let rec eval_var (g:Type) (a:Type) v env = match v with
	| O 'gg 'aa -> snd #'gg #a env
 	| S 'gg 'aa 'b u -> eval_var 'gg a u (fst #'gg #'b env)

val eval: g:Type -> a:Type -> t:tm g a -> g -> Tot a (decreases %[t;0])
let rec eval (g:Type) (a:Type) t env = match t with
 | Var v -> eval_var g a v env

 | Lam 'gg 'arg 'res body ->
   Clos (tm (g * 'arg) 'res * g)
        #'arg #'res
		     (body, env)
		     (fun (body, env) x -> eval (g * 'arg) 'res body (env, x))
   //can hoist this fun to the top to be mutually recursive with eval since it's now a closed term

 | App 'gg 'aa 'bb e1 e2 -> apply (eval g (closure 'aa a) e1 env)
                                  (eval g 'aa e2 env)

val eval': g:Type -> a:Type -> t:tm g a -> g -> Tot a (decreases %[t;0])
val eval_lam_hoist: g:Type -> arg:Type -> res:Type -> s:(tm (g * arg) res * g) -> arg -> Tot res (decreases %[(fst s); 1])
let rec eval' (g:Type) (a:Type) t env = match t with
  | Var v -> eval_var g a v env

  | Lam 'gg 'arg 'res body ->
    Clos (tm (g * 'arg) 'res * g)
         #'arg
         #'res
		     (body, env)
         (eval_lam_hoist g 'arg 'res)

  | App 'gg 'aa 'bb e1 e2 -> apply (eval' g (closure 'aa a) e1 env)
                                   (eval' g 'aa e2 env)

and eval_lam_hoist (g:Type) (arg:Type) (res:Type) (body, env) x =
    eval' (g * arg) res body (env, x)
