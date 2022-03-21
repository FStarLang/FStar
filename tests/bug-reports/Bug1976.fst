module Bug1976

noeq
type class1 (index: Type0) =
  | Class1:
    s:(index -> Type0) ->
    t:(index -> Type0) ->
    v:(#i:index -> s i -> t i) ->
    class1 index

noeq
type class2 index =
  | Class2:
    c1:class1 index ->
    c1':class1 index ->
    f: (#i:index -> c1.t i -> c1'.t i -> c1.t i) ->
    class2 index
