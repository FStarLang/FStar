module Eval.DB

noeq type var : Type -> Type -> Type =
   | O : g:Type -> a:Type -> var (g * a) a
   | S : g:Type -> a:Type -> b:Type -> var g a -> var (g * b) a

noeq type tm : Type -> Type -> Type =
   | Var : g:Type -> a:Type -> var g a -> tm g a
   | Lam : g:Type -> a:Type -> b:Type -> body:tm (g * a) b -> tm g (a -> Tot b)
   | App : g:Type -> a:Type -> b:Type -> e1:tm g (a -> Tot b) -> e2:tm g a -> tm g b

val eval_var : g:Type -> a:Type -> var g a -> g -> Tot a
let rec eval_var (g:Type) (a:Type) v env = match v with
   | O 'g0 '_ -> snd #'g0 #a env
   | S 'g0 'a0 'b0 u -> eval_var 'g0 'a0 u (fst #'g0 #'b0 env)

val eval: g:Type -> a:Type -> tm g a -> g -> Tot a
let rec eval (g:Type) (a:Type) t env = match t with
 | Var _ _ v -> eval_var g a v env
 | Lam 'gg 'arg 'res body ->
    (fun (x:'arg) -> eval (g * 'arg) 'res body (env,x))
 | App 'gg 'arg 'res e1 e2 ->
    (eval g ('arg -> Tot 'res) e1 env <: 'arg -> Tot 'res (* still need this silly annotation; TODO, fix *))
    (eval g 'arg e2 env)

