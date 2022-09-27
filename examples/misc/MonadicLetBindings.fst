module MonadicLetBindings
open FStar.List.Tot

/// This module illustrates monadic let bindings, which exist in
/// OCaml, see https://v2.ocaml.org/manual/bindingops.html.
///
/// Monadic let bindings allows the user to write custom _let
/// operators_ to ease writing monadic programs.
///
/// F* supports:
///
///  - [let] operators [let*], that represent the _bind_ operator of a
///    monad or the _map_ operator of a functor;
///
///  - [and] operators [and*], that represent a _pair_ operation
///    (a.k.a. a reformulation of the [<*>] operator of an
///    applicative);
///
///  - monadic pattern matching [match*], desugaring into (1) a [let]
///    operator [let*] and (2) a normal [match];
///
///  - and monadic sequences [x ;* y], that desugars into
///    [let* _ = x in y].
///
/// Note that above [*] stands for any non-empty sequence of character
/// in the class "!$%&*+-.<>=?^|~:@#\\/".
///
/// Also, F* support the lightweight do notations [x <-- y; z] and [x
/// ;; z] that desugars into [bind y (fun x -> z)] and [bind y (fun _
/// -> z)], using the ambient identifier `bind`. However, this do
/// notation is deprecated in favor of monadic let bindings.

(**** The [option] monad *)
// Bind operator
let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

// Sort of applicative
let (and?) (x: option 'a) (y: option 'b): option ('a * 'b)
  = match x, y with
  | Some x, Some y -> Some (x, y)
  | _ -> None

let head: list _ -> option _
  = function | v::_ -> Some v
             |   _ -> None

let option_example (a b: list (int * int)) (c: option bool) =
  let? haL, haR = head a
  and? hbL, hbR = head b in
  match? c with
  | true  -> Some (haL + hbL)
  | false -> Some (haR + hbR)

let let_punning (a: option int)
  = let? a in // equivalent to [let? a = a in]
    Some (a + 10)

let sequence_example (validate: int -> option int) (x: int)
  = validate x ;?
    if x = 0 then None
             else Some (42 / x)

let _ = assert_norm (option_example [(1,2)] [(3,4)] (Some true) == Some 4)
let _ = assert_norm (option_example [] [(3,4)] (Some true) == None)

(**** How does let operators desugar? *)
/// The [let<OP>] syntax is desugared into function applications.
/// For instance, [sugared1] below desugars into [desugared1].
/// Using Emacs's F* mode, it is easy to evaluate [sugared1] to show to
/// what it desugar exactly, using the command [fstar-eval] (or the
/// keybinding <C-c C-s C-e>)
let sugared1 (let*) (and*) ex ey ez f
  = let* x = ex
    and* y = ey
    and* z = ez in
    f x y z
let desugared1 op_let_Star op_and_Star ex ey ez f
    = op_let_Star (op_and_Star (op_and_Star ex ey) ez)
        (fun ((x, y), z) -> f x y z)

let sugared2 (let?) (ex: option int): option int
  = match? ex with
  | 0 -> None
  | x -> Some (10 / x)
let desugared2 op_let_Question ex
  = op_let_Question ex (fun x -> match x with
                       | 0 -> None
                       | x -> Some (10 / x))

let sugared3 (let?) ex
  = ex ;?
    Some 1
let desugared3 op_let_Question ex
  = op_let_Question ex (fun _ -> Some 1)

(**** The [list] monad *)
let ( let:: ) (l: list 'a) (f: 'a -> list 'b): list 'b
  = flatten (map f l)

let rec zip (a: list 'a) (b: list 'b): list ('a * 'b)
  = match a, b with
  | ha::ta, hb::tb -> (ha,hb)::zip ta tb
  | _            -> []

let ( and:: ) (a: list 'a) (b: list 'b): list ('a * 'b)
  = zip a b

let list_example1 =
  let:: x = [10;20;30] in
  [x + 1; x + 2; x + 3]

let _ = assert_norm (list_example1 == [11;12;13;21;22;23;31;32;33])

let list_example2 =
  let:: x = [10;20;30]
  and:: y = ["A";"B";"C"] in
  [x + 5, y ^ "!"]

let _ = assert_norm (list_example2 == [15, "A!"; 25, "B!"; 35, "C!"])

(**** Example: evaluating expressions *)
type exp =
  | Const: int -> exp
  | Addition: exp -> exp -> exp
  | Division: exp -> exp -> exp

let rec eval (e: exp): option int
  = match e with
  | Const x -> Some x
  | Addition x y -> let? x = eval x
                   and? y = eval y in
                   Some (x + y)
  | Division x y -> match? eval y with
                 | 0 -> None
                 | y -> let? x = eval x in
                       Some (x / y)


(**** [pair] is just a reformulation of [<*>] *)
// Section 7 of McBride & Patterson "Applicative programming with
// effects" [https://www.staff.city.ac.uk/~ross/papers/Applicative.pdf]
let applicative_eq (m: Type -> Type) (fmap: (#a:Type -> #b:Type -> (a -> b) -> m a -> m b)) =
  let (<*>) (pair: (#a:Type -> #b:Type -> m a -> m b -> m (a * b)))
    : #a:Type -> #b:Type -> m (a -> b) -> m a -> m b
    = fun f o -> fmap (fun (f, x) -> f x) (pair f o) in
  let pair ((<*>): (#a:Type -> #b:Type -> m (a -> b) -> m a -> m b))
    : #a:Type -> #b:Type -> m a -> m b -> m (a * b)
    = fun x y -> fmap Mktuple2 x <*> y in
  ()
