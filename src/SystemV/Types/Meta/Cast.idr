module SystemV.Types.Meta.Cast

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Utilities
import SystemV.Types.Direction
import SystemV.Types.Meta
import SystemV.Types.Meta.Equality
import SystemV.Types.Meta.Equiv

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
  validCastDir : (l,r : Direction)
                     -> DecInfo Cast.Direction.Error (ValidDirCast l r)

  validCastDir IN IN = Yes InsertEndpointXX
  validCastDir OUT OUT = Yes InsertEndpointXX
  validCastDir INOUT INOUT = Yes InsertEndpointXX
  validCastDir IN INOUT = Yes InsertEndpointIB
  validCastDir OUT INOUT = Yes InsertEndpointOB

  validCastDir IN OUT = No (CannotCast IN OUT) ioNotCastable
  validCastDir OUT IN = No (CannotCast OUT IN) oiNotCastable

  validCastDir INOUT IN  = No (CannotCast INOUT IN)  biNotCastable
  validCastDir INOUT OUT = No (CannotCast INOUT OUT) boNotCastable

data Castable : (typeA : Meta (IDX VALUE)) -> Type where
  IsCastable : Castable (PortVal type dir)

funcNotCastable : Castable (FuncTy x y) -> Void
funcNotCastable IsCastable impossible

moduleNotCastable : Castable (ModuleVal) -> Void
moduleNotCastable IsCastable impossible

chanNotCastable : Castable (ChanVal type) -> Void
chanNotCastable IsCastable impossible

paramNotCastable : Castable (ParamVal) -> Void
paramNotCastable IsCastable impossible

unitNotCastable : Castable (UnitVal) -> Void
unitNotCastable IsCastable impossible

castable : (type : Meta (IDX VALUE)) -> Dec (Castable type)
castable (FuncTy x y) = No funcNotCastable
castable ModuleVal = No moduleNotCastable
castable (ChanVal type) = No chanNotCastable
castable (PortVal type dir) = Yes IsCastable
castable ParamVal = No paramNotCastable
castable UnitVal = No unitNotCastable

data Error = DirNotCast Cast.Direction.Error
           | TypesNotEquiv Equiv.Error
           | NotCastableFrom (Meta (IDX VALUE))
           | NotCastableTo (Meta (IDX VALUE))

public export
data ValidCast : (typeA, typeB : Meta (IDX VALUE))
              -> Type
  where
   CanCast : (castDir : ValidDirCast           dirA               dirB)
          -> (castTy  : EquivTypes         tyA                tyB)
                     -> ValidCast (PortVal tyA dirA) (PortVal tyB dirB)

cannotCastFrom : (Castable type -> Void)
          -> ValidCast type typeB
          -> Void
cannotCastFrom contra (CanCast castDir castTy) = contra IsCastable

cannotCastTo : (Castable typeB -> Void)
          -> ValidCast type typeB
          -> Void
cannotCastTo contra (CanCast castDir castTy) = contra IsCastable

dirNotCastable : (contra : ValidDirCast dirA dirB -> Void)
              -> (prf    : ValidCast (PortVal typeA dirA) (PortVal typeB dirB))
                        -> Void
dirNotCastable contra (CanCast castDir castTy) = contra castDir

typeNotEquiv : (contra : EquivTypes a b -> Void)
            -> (prf    : ValidCast (PortVal a dirA) (PortVal b dirB))
                      -> Void
typeNotEquiv contra (CanCast castDir castTy) = contra castTy

export
validCast : (typeA, typeB : Meta (IDX VALUE))
                         -> DecInfo Cast.Error (ValidCast typeA typeB)
validCast typeA typeB with (castable typeA)
  validCast (PortVal typeA dirA) typeB | (Yes IsCastable) with (castable typeB)
    validCast (PortVal typeA dirA) (PortVal typeB dirB) | (Yes IsCastable) | (Yes IsCastable) with (validCastDir dirA dirB)
      validCast (PortVal typeA dirA) (PortVal typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfWhy) with (equivDataTypes typeA typeB)
        validCast (PortVal typeA dirA) (PortVal typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfWhy) | (Yes prfTy) = Yes (CanCast prfWhy prfTy)
        validCast (PortVal typeA dirA) (PortVal typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfWhy) | (No msgWhyNot prfWhyNot) = No (TypesNotEquiv msgWhyNot) (typeNotEquiv prfWhyNot)
      validCast (PortVal typeA dirA) (PortVal typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (No msgWhyNot prfWhyNot) = No (DirNotCast msgWhyNot) (dirNotCastable prfWhyNot)
    validCast (PortVal type dir) typeB | (Yes IsCastable) | (No contra) = No (NotCastableTo typeB) (cannotCastTo contra)
  validCast typeA typeB | (No contra) = No (NotCastableFrom typeA) (cannotCastFrom contra)
