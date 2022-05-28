module TemplateLiterals

module T = FStar.Tactics
open FStar.List.Tot

(**** Generic interface for quasiquoters *)
noeq type quasiquoter = {
  t: Type u#t;
  process: list (either string T.term) -> T.Tac t;
  make_type:  t -> T.Tac unit;
  make_value: t -> T.Tac unit;
}

let synth_quasiquote
    (qq: quasiquoter u#qq)
    (input: unit -> T.Tac (list (either string T.term)))
    (#[(let data = qq.process (input ()) in
        T.exact (quote data))] data : qq.t)
    (#[qq.make_type data]    typ  : Type u#t)
    (#[qq.make_value data]   value:  typ)
    ()
    = value

(**** Helpers to unquote terms *)
let name_of_compview: T.comp_view -> string = function
  | T.C_Total     _ _     -> "Total"
  | T.C_GTotal    _ _     -> "GTotal"
  | T.C_Lemma     _ _ _   -> "Lemma"
  | T.C_Eff       _ n _ _ -> T.implode_qn n

/// Given [a] a type of any universe and [v] a value of type [a],
/// [wrapper] is of type unit, and is irreducible. It is a trick so
/// that we don't have to bother with types and universes when
/// unquoting terms.
irreducible let wrapper (a: Type u#a) (v: a): unit = ()

/// [eval_term] evaluates a term [t] in an environment [e], where [t]
/// is either a [Tot] computation or a [Tac] computation.
let eval_term (e: T.env) (t: T.term): T.Tac T.term
  = let open FStar.Tactics in
    let comp = try tcc e t with | e -> raise e in
    match inspect_comp comp with
  | C_Eff _ ["Prims"; "PURE"] _ _ | C_Total _ _ -> t
  | C_Eff _ ["FStar"; "Tactics"; "Effect"; _] ret _
      -> // [tac] is [fun (dummy:()) -> wrapper t]
        let tac: term = mk_abs [fresh_binder_named "dummy" (`unit)] (mk_e_app (`wrapper) [ret; t]) in
        // thus, we can unquote [tac] as a [unit -> Tac unit] computation, and run it
        let u: unit = (unquote #(unit -> Tac unit) tac) () in
        // we normalize the result, that should be of shape [wrapper … result]
        let fn, args = collect_app (quote u) in
        begin match args with
        | [(a,Q_Explicit);(v,Q_Explicit)] -> v // correct shape (TODO: we assume [fn] is [wrapper] here)
        | _ -> fail "[eval] E0: after evaluation of tactic [t], the normalized result is not of the shape [wrapper … …]"
        end
  | cv -> fail ("[eval] E1: effect ["^name_of_compview cv^"] not supported")

(**** A typeclass for showing values of various types *)
class showTC (a: Type) = { show: a -> string }
instance _: showTC int = { show = string_of_int; }
instance _: showTC nat = { show = string_of_int; }
instance _: showTC string = { show = id; }

instance showList {| showTC 'a |}: showTC (list 'a)
  = { show = (fun l -> "[" ^ String.concat ", " (map show l) ^ "]"); }

(**** A [str] quasiquoter, a.k.a. template literals *)

let str_qq = {
    t = string;
    process = (fun l -> String.concat "" (T.map (function
                                             | Inl raw -> raw
                                             | Inr t -> T.unquote (eval_term (T.top_env ()) (`(show (`#t))))
                                             ) l));
    make_type = (fun _ -> T.exact (`eqtype_as_type string));
    make_value = (fun x -> T.exact (quote x)); }

let str = synth_quasiquote str_qq



let synth_quasiquote'
    (qq: quasiquoter u#qq)
    (input: unit -> T.Tac (list (either string T.term)))
    (#[(let data = qq.process (input ()) in
        T.exact (quote data))] data : qq.t)
    (#[qq.make_type data]    typ  : Type u#t)
    (#[qq.make_value data]   value:  typ)
    ()
    = value

let str' = synth_quasiquote' str_qq (fun _ -> [Inl "x"]) ()

(**** Examples *)
(***** Basic example *)
let simple =
  let x = 1 in
  let y = 2 in
  let z = "hello" in
  [str|list=`[x;y] x=`x, y=`y rev=`(rev [x;y]), and z is `z|]

(***** Groceries *)
let groceries (euros: nat) (items: list (int * string)) =
  let items = map (fun (n, item) -> [str|`n `item`(if n=1 then "" else "s")|]) items in
  [str|You want to buy `items, and you have `euros €|]

let _ = T.run_tactic (fun _ -> T.print (groceries 25 [2, "orange"; 6, "apple"; 1, "banana"]))
(* This prints:
You want to buy [2 oranges, 6 apples, 1 banana], and you have 25 €
*)

(***** Showing lists of tasks *)
let concatMap sep f l = String.concat sep (map f l)
type priority = | A | B | C
type task = { title: string
            ; priority: priority
            ; details: list string }
instance _: showTC priority = { show = function | A -> "A" | B -> "B" | C -> "C" }

let showTC_todos (name: string) (tasks: list task): string =
   [str|Hi `name, today you've got `(length tasks) tasks left:
`(concatMap "\n" (fun ({title; priority; details}) -> [str| • `title [`priority]:
`(concatMap "\n" (fun participant -> [str|   ∘ `participant|]) details)|]) tasks)

Good luck!
|]

let example = showTC_todos "Alice" [
  {title = "foo"; priority = A; details = ["do X"; "do Y"]};
  {title = "bar"; priority = C; details = ["do Z"; "something"; "something else"]}
]

let _ = T.run_tactic (fun _ -> T.print example)
(* This prints:
Hi Alice, today you've got 2 tasks left:
 • foo [A]:
   ∘ do X
   ∘ do Y
 • bar [C]:
   ∘ do Z
   ∘ something
   ∘ something else

Good luck!
*)

