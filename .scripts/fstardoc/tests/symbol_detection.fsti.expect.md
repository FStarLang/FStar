#### c_True

[`c_True`](#c_True) is the singleton inductive type---it is trivially
inhabited. Like `c_False`, [`c_True`](#c_True) is seldom used. We instead use
its "squashed" variants, `True`

```fstar
type c_True = | T
```

#### get_equality

Produce equality as a `Type` if provable from context.

```fstar
val get_equality
  (#t:Type)
  (a b: t)
  : Pure (a == b)
    (requires (a == b))
    (ensures (fun _ -> True))
```

#### l_True

[`l_True`](#l_True) has a special bit of syntactic sugar. It is written just
as "True" and rendered in the ide as `True`. It is a squashed version
of constructive truth, [`c_True`](#c_True).

```fstar
[@"tac_opaque" smt_theory_symbol]
let l_True :logical = squash c_True
```

#### PURE

Introduces the PURE effect.

```fstar
total
new_effect {
  PURE : a:Type -> wp:pure_wp a -> Effect
  with return_wp    = pure_return
     ; bind_wp      = pure_bind_wp
     ; if_then_else = pure_if_then_else
     ; ite_wp       = pure_ite_wp
     ; stronger     = pure_stronger
     ; close_wp     = pure_close_wp
     ; trivial      = pure_trivial
}
```

#### hasEq

A predicate to express when a type supports decidable equality
The type-checker emits axioms for [`hasEq`](#hasEq) for each inductive type

```fstar
assume type hasEq: Type -> GTot Type0
```

#### Lemma

[`Lemma`](#Lemma) is a very widely used effect abbreviation.

```fstar
effect Lemma (a:Type) (pre:Type) (post:squash pre -> Type) (pats:list pattern) =
       Pure a pre (fun r -> post ())
```
