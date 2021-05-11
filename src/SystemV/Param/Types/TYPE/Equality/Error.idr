module SystemV.Param.Types.TYPE.Equality.Error

import SystemV.Param.Types.TYPE

%default total

namespace Equality
  public export
  data Error = KindMismatch Universe Universe
             | TypeMismatch (TYPE a) (TYPE a)


-- [ EOF ]
