module SystemV.Annotated.Types.TYPE.Equality.Error

import SystemV.Annotated.Types.TYPE

%default total

namespace Equality
  public export
  data Error = KindMismatch Universe Universe
             | TypeMismatch (TYPE a) (TYPE a)
             | SensitivityMismatch Sensitivity Sensitivity
             | IntentionMismatch Intention Intention


-- [ EOF ]
