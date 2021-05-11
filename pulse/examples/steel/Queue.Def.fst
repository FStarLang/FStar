module Queue.Def

open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.FractionalPermission
open Steel.SelReference

#push-options "--__no_positivity"
noeq
type cell (a:Type0) = {
  data : a;
  next : t a;
}
and t a = ref (cell a)
#pop-options
