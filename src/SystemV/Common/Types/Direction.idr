||| Structures to describe port direction.
module SystemV.Common.Types.Direction

import Decidable.Equality
import Toolkit.Decidable.Informative

%default total

public export
data Direction = IN | OUT | INOUT


ioNotEqual : (IN === OUT) -> Void
ioNotEqual Refl impossible

ibNotEqual : (IN === INOUT) -> Void
ibNotEqual Refl impossible

obNotEqual : (OUT === INOUT) -> Void
obNotEqual Refl impossible

export
decEq : (l,r : Direction)
            -> Dec (l === r)
decEq IN IN = Yes Refl
decEq OUT OUT = Yes Refl
decEq INOUT INOUT = Yes Refl

decEq IN OUT = No ioNotEqual
decEq OUT IN = No (negEqSym ioNotEqual)

decEq IN INOUT = No ibNotEqual
decEq INOUT IN = No (negEqSym ibNotEqual)

decEq OUT INOUT = No obNotEqual
decEq INOUT OUT = No (negEqSym obNotEqual)

||| Standard decidable equality.
export
DecEq Direction where
  decEq = Direction.decEq

namespace Flow

  ||| A Valid Flow is one that goes 'left' to 'right' between an
  ||| output and input port.
  public export
  data ValidFlow : (l,r : Direction) -> Type where
    FlowOI : ValidFlow OUT   IN
    FlowBI : ValidFlow INOUT IN
    FlowOB : ValidFlow OUT   INOUT
    FlowBB : ValidFlow INOUT INOUT

  public export
  data Error = CannotFlow Direction Direction

  boNoFlow : ValidFlow INOUT OUT -> Void
  boNoFlow FlowOI impossible
  boNoFlow FlowBI impossible
  boNoFlow FlowOB impossible
  boNoFlow FlowBB impossible

  ooNoFlow : ValidFlow OUT OUT -> Void
  ooNoFlow FlowOI impossible
  ooNoFlow FlowBI impossible
  ooNoFlow FlowOB impossible
  ooNoFlow FlowBB impossible

  iiNoFlow : ValidFlow IN IN -> Void
  iiNoFlow FlowOI impossible
  iiNoFlow FlowBI impossible
  iiNoFlow FlowOB impossible
  iiNoFlow FlowBB impossible

  ioNoFlow : ValidFlow IN OUT -> Void
  ioNoFlow FlowOI impossible
  ioNoFlow FlowBI impossible
  ioNoFlow FlowOB impossible
  ioNoFlow FlowBB impossible

  ibNoFlow : ValidFlow IN INOUT -> Void
  ibNoFlow FlowOI impossible
  ibNoFlow FlowBI impossible
  ibNoFlow FlowOB impossible
  ibNoFlow FlowBB impossible

  ||| Do these two directions represent a valid flow.
  export
  validFlow : (l,r : Direction)
                  -> DecInfo Flow.Error (ValidFlow l r)
  validFlow OUT IN = Yes FlowOI
  validFlow OUT INOUT = Yes FlowOB
  validFlow INOUT IN = Yes FlowBI
  validFlow INOUT INOUT = Yes FlowBB

  validFlow INOUT OUT = No (CannotFlow INOUT OUT) boNoFlow
  validFlow OUT   OUT = No (CannotFlow OUT   OUT) ooNoFlow

  validFlow IN IN = No (CannotFlow IN IN) iiNoFlow
  validFlow IN OUT = No (CannotFlow IN OUT) ioNoFlow
  validFlow IN INOUT = No (CannotFlow IN INOUT) ibNoFlow


-- [ EOF ]
