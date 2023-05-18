module Queue.Def

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

/// The definition of the basic datatypes of a queue.
/// A cell contains a value, and a pointer to the next element
/// A queue is simply a pointer to a cell

#push-options "--__no_positivity"
noeq
type cell (a:Type0) = {
  data : a;
  next : t a;
}
and t a = ref (cell a)
#pop-options
