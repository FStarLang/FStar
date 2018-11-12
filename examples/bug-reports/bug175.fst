module Bug175

type exp =
  | EApp : exp  -> exp -> exp

type heap = int -> Tot int

type config = heap * exp

noeq type step : config -> Type =
  | SApp1 : h:heap ->
            e1:exp ->
            e2:exp ->
            step (h, EApp e1 e2)
  | SApp2 : h:heap ->
            e1:exp ->
            e2:exp ->
            step (h, e2) ->
            step (h, EApp e1 e2)
