module Queue.Def

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

#push-options "--__no_positivity"
noeq
type cell (a:Type0) = {
  data : a;
  next : t a;
}
and t a = ref (cell a)
#pop-options
