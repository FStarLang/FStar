module Bug2912

let id x = x
type pack = (t:Type0 & id t)
