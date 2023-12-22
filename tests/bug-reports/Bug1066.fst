module Bug1066

assume val m : Type -> Type
assume val return_m : #a:Type -> a -> m a
assume val bind_m : #a:Type -> #b:Type -> m a -> (a -> m b) -> m b
assume val push_m : #a:Type -> #b:(a -> Type) -> (x:a -> m (b x)) -> m (x:a -> b x)

val push_sum : #a:Type -> #b:(a -> Type) ->
                  dtuple2 a (fun (x:a) -> m (b x)) -> m (dtuple2 a b)
let push_sum (#a:Type) (#b:(a -> Type)) (p : (dtuple2 a (fun (x:a) -> m (b x)))) =
    match p with
    | Mkdtuple2 x y ->
        bind_m #(b x) (* #(dtuple2 a b) *) y (fun (y' : b x) ->
        return_m (* #(dtuple2 a b) *) (Mkdtuple2 x y'))
