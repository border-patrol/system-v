module SystemV.Types.TYPE.Equality.Error

import SystemV.Types.TYPE

%default total

namespace Equality
  public export
  data Error = KindMismatch Universe Universe
             | TypeMismatch (TYPE a) (TYPE a)


-- [ EOF ]
