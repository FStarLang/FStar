module Bug186

type form =
| FImpl   : form -> form -> form
| FForall : #a:Type -> (a -> form) -> form

type valid : form -> Type =
  | VImpl       : #f1:form    -> 
                  #f2:form     ->
                  (f : valid f1 -> valid f2) -> 
                  valid (FImpl f1 f2)
  | VForall     : #a:Type     ->
                  #p:(a -> Tot form)->
                  f: (x:a-> Tot (valid (p x)))->
                  valid (FForall p)

val hoare_consequence : f:form -> valid f -> h:heap -> Tot unit
let hoare_consequence f v h =
  let VForall fpp' = v in
(*  ignore (fpp' h) -- patterns are incomplete *)
  assert (is_VImpl (fpp' h));(*BUG: adding this makes F* explode *)
  magic()
