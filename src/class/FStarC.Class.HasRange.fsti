module FStarC.Class.HasRange
#push-options "--MLish --MLish_effect FStarC.Effect"

open FStarC.Effect
open FStarC.Range.Type

class hasRange (a:Type) = {
  pos : a -> range;
  setPos : range -> a -> a;
}

instance val hasRange_range : hasRange range
