module SystemV.Base.Types.TYPE.Equality.Error

import SystemV.Base.Types.TYPE

%default total

namespace Equality
  public export
  data Error = KindMismatch Universe Universe
             | TypeMismatch (TYPE a) (TYPE a)


-- [ EOF ]
