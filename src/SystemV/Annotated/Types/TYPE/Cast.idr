module SystemV.Annotated.Types.TYPE.Cast

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Utilities

import SystemV.Common.Types.Direction

import SystemV.Annotated.Types.TYPE
import SystemV.Annotated.Types.TYPE.Equality
import SystemV.Annotated.Types.TYPE.Equiv

%default total

namespace Direction

  public export
  data ValidDirCast : (l,r : Direction) -> Type where
    InsertEndpointIB : ValidDirCast IN  INOUT
    InsertEndpointOB : ValidDirCast OUT INOUT
    InsertEndpointXX : ValidDirCast a   a

  ioNotCastable : ValidDirCast IN OUT -> Void
  ioNotCastable InsertEndpointIB impossible
  ioNotCastable InsertEndpointOB impossible
  ioNotCastable InsertEndpointXX impossible

  oiNotCastable : ValidDirCast OUT IN -> Void
  oiNotCastable InsertEndpointIB impossible
  oiNotCastable InsertEndpointOB impossible
  oiNotCastable InsertEndpointXX impossible

  biNotCastable : ValidDirCast INOUT IN -> Void
  biNotCastable InsertEndpointIB impossible
  biNotCastable InsertEndpointOB impossible
  biNotCastable InsertEndpointXX impossible

  boNotCastable : ValidDirCast INOUT OUT -> Void
  boNotCastable InsertEndpointIB impossible
  boNotCastable InsertEndpointOB impossible
  boNotCastable InsertEndpointXX impossible

  public export
  data Error = CannotCast Direction Direction

  export
  cast : (l,r : Direction)
             -> DecInfo Cast.Direction.Error (ValidDirCast l r)

  cast IN IN = Yes InsertEndpointXX
  cast OUT OUT = Yes InsertEndpointXX
  cast INOUT INOUT = Yes InsertEndpointXX
  cast IN INOUT = Yes InsertEndpointIB
  cast OUT INOUT = Yes InsertEndpointOB

  cast IN OUT = No (CannotCast IN OUT) ioNotCastable
  cast OUT IN = No (CannotCast OUT IN) oiNotCastable

  cast INOUT IN  = No (CannotCast INOUT IN)  biNotCastable
  cast INOUT OUT = No (CannotCast INOUT OUT) boNotCastable

data Castable : (typeA : TYPE (IDX TERM)) -> Type where
  IsCastable : Castable (PortTy type dir sense intent)

funcNotCastable : Castable (FuncTy x y) -> Void
funcNotCastable IsCastable impossible

moduleNotCastable : Castable (ModuleTy) -> Void
moduleNotCastable IsCastable impossible

chanNotCastable : Castable (ChanTy type sense dir) -> Void
chanNotCastable IsCastable impossible

unitNotCastable : Castable (UnitTy) -> Void
unitNotCastable IsCastable impossible

castable : (type : TYPE (IDX TERM)) -> Dec (Castable type)
castable (FuncTy x y) = No funcNotCastable
castable ModuleTy = No moduleNotCastable
castable (ChanTy type sense intent) = No chanNotCastable
castable (PortTy type dir sense intent) = Yes IsCastable
castable UnitTy = No unitNotCastable

public export
data Error = DirNotCast Cast.Direction.Error
           | TypesNotEquiv Equiv.Error
           | NotCastableFrom (TYPE (IDX TERM))
           | NotCastableTo (TYPE (IDX TERM))
           | SensitivityNotCompat Sensitivity.Error
           | IntentionNotCompat Intention.Error

public export
data ValidCast : (typeA, typeB : TYPE (IDX TERM))
              -> Type
  where
   CanCast : (castTy     : EquivTypes tyA tyB)
          -> (castDir    : ValidDirCast dirA dirB)
          -> (castSense  : Compatible sA sB)
          -> (castIntent : Compatible iA iB)
                        -> ValidCast (PortTy tyA dirA sA iA)
                                     (PortTy tyB dirB sB iB)

cannotCastFrom : (Castable type -> Void)
          -> ValidCast type typeB
          -> Void
cannotCastFrom f (CanCast castTy castDir castSense castIntent) = f IsCastable


cannotCastTo : (Castable typeB -> Void)
          -> ValidCast type typeB
          -> Void
cannotCastTo f (CanCast castTy castDir castSense castIntent) = f IsCastable


dirNotCastable : (contra : ValidDirCast dirA dirB -> Void)
              -> (prf    : ValidCast (PortTy typeA dirA sA iA) (PortTy typeB dirB sB iB))
                        -> Void
dirNotCastable contra (CanCast castTy castDir castSense castIntent) = contra castDir


typeNotEquiv : (contra : EquivTypes a b -> Void)
            -> (prf    : ValidCast (PortTy a dirA sA iA) (PortTy b dirB sB iB))
                      -> Void
typeNotEquiv contra (CanCast castTy castDir castSense castIntent) = contra castTy


sensNotCompat : (Compatible sA sB -> Void) -> ValidCast (PortTy tA dA sA iA) (PortTy tB dB sB iB) -> Void
sensNotCompat f (CanCast castTy castDir castSense castIntent) = f castSense

intentNotCompat : (Compatible iA iB -> Void) -> ValidCast (PortTy tA dA sA iA) (PortTy tB dB sB iB) -> Void
intentNotCompat f (CanCast castTy castDir castSense castIntent) = f castIntent

export
cast : (typeA, typeB : TYPE (IDX TERM))
                         -> DecInfo Cast.Error
                                    (ValidCast typeA typeB)
cast typeA typeB with (castable typeA)
  cast (PortTy tA dA sA iA) typeB | (Yes IsCastable) with (castable typeB)
    cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) with (equivDataTypes tA tB)
      cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) with (cast dA dB)
        cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) | (Yes prfD) with (compatible sA sB)
          cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) | (Yes prfD) | (Yes prfS) with (compatible iA iB)
            cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) | (Yes prfD) | (Yes prfS) | (Yes prfI)
              = Yes (CanCast prfT prfD prfS prfI)
            cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) | (Yes prfD) | (Yes prfS) | (No msgWhyNot prfWhyNot)
              = No (IntentionNotCompat msgWhyNot) (intentNotCompat prfWhyNot)
          cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) | (Yes prfD) | (No msgWhyNot prfWhyNot)
            = No (SensitivityNotCompat msgWhyNot) (sensNotCompat prfWhyNot)

        cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfT) | (No msgWhyNot prfWhyNot)
          = No (DirNotCast msgWhyNot) (dirNotCastable prfWhyNot)
      cast (PortTy tA dA sA iA) (PortTy tB dB sB iB) | (Yes IsCastable) | (Yes IsCastable) | (No msgWhyNot prfWhyNot)
        = No (TypesNotEquiv msgWhyNot) (typeNotEquiv prfWhyNot)

    cast (PortTy tA dA sA iA) typeB | (Yes IsCastable) | (No contra)
      = No (NotCastableTo typeB) (cannotCastTo contra)
  cast typeA typeB | (No contra)
    = No (NotCastableFrom typeA) (cannotCastFrom contra)

-- [ EOF ]
