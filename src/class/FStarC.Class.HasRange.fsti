module FStarC.Class.HasRange

open FStarC.Effect
open FStarC.Range.Type

class hasRange (a:Type) = {
  pos : a -> ML range;
  setPos : range -> a -> ML a;
}

instance val hasRange_range : hasRange range
