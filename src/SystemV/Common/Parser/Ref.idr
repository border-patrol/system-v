module SystemV.Common.Parser.Ref

import Toolkit.Data.Location

%default total

public export
record Ref where
  constructor MkRef
  span : FileContext
  get  : String


-- [ EOF ]
