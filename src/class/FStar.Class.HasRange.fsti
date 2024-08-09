module FStar.Class.HasRange

open FStar.Compiler.Effect
open FStar.Compiler.Range

class hasRange (a:Type) = {
  pos : a -> range;
  setPos : range -> a -> a;
}
