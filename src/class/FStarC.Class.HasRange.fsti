module FStarC.Class.HasRange

open FStarC.Effect
open FStarC.Range.Type

class hasRange (a:Type) = {
  pos : a -> range;
  setPos : range -> a -> a;
}

instance val hasRange_range : hasRange range
