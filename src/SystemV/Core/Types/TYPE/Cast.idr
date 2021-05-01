module SystemV.Core.Types.TYPE.Cast

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Utilities

import SystemV.Common.Types.Direction

import SystemV.Core.Types.TYPE
import SystemV.Core.Types.TYPE.Equality
import SystemV.Core.Types.TYPE.Equiv

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

data Castable : (typeA : TYPE (IDX TERM)) -> Type where
  IsCastable : Castable (PortTy type dir)

funcNotCastable : Castable (FuncTy x y) -> Void
funcNotCastable IsCastable impossible

moduleNotCastable : Castable (ModuleTy) -> Void
moduleNotCastable IsCastable impossible

chanNotCastable : Castable (ChanTy type) -> Void
chanNotCastable IsCastable impossible

unitNotCastable : Castable (UnitTy) -> Void
unitNotCastable IsCastable impossible

castable : (type : TYPE (IDX TERM)) -> Dec (Castable type)
castable (FuncTy x y) = No funcNotCastable
castable ModuleTy = No moduleNotCastable
castable (ChanTy type) = No chanNotCastable
castable (PortTy type dir) = Yes IsCastable
castable UnitTy = No unitNotCastable

public export
data Error = DirNotCast Cast.Direction.Error
           | TypesNotEquiv Equiv.Error
           | NotCastableFrom (TYPE (IDX TERM))
           | NotCastableTo (TYPE (IDX TERM))

public export
data ValidCast : (typeA, typeB : TYPE (IDX TERM))
              -> Type
  where
   CanCast : (castDir : ValidDirCast           dirA               dirB)
          -> (castTy  : EquivTypes         tyA                tyB)
                     -> ValidCast (PortTy tyA dirA) (PortTy tyB dirB)

cannotCastFrom : (Castable type -> Void)
          -> ValidCast type typeB
          -> Void
cannotCastFrom contra (CanCast castDir castTy) = contra IsCastable

cannotCastTo : (Castable typeB -> Void)
          -> ValidCast type typeB
          -> Void
cannotCastTo contra (CanCast castDir castTy) = contra IsCastable

dirNotCastable : (contra : ValidDirCast dirA dirB -> Void)
              -> (prf    : ValidCast (PortTy typeA dirA) (PortTy typeB dirB))
                        -> Void
dirNotCastable contra (CanCast castDir castTy) = contra castDir

typeNotEquiv : (contra : EquivTypes a b -> Void)
            -> (prf    : ValidCast (PortTy a dirA) (PortTy b dirB))
                      -> Void
typeNotEquiv contra (CanCast castDir castTy) = contra castTy

export
validCast : (typeA, typeB : TYPE (IDX TERM))
                         -> DecInfo Cast.Error
                                    (ValidCast typeA typeB)
validCast typeA typeB with (castable typeA)
  validCast (PortTy typeA dirA) typeB | (Yes IsCastable) with (castable typeB)
    validCast (PortTy typeA dirA) (PortTy typeB dirB) | (Yes IsCastable) | (Yes IsCastable) with (validCastDir dirA dirB)
      validCast (PortTy typeA dirA) (PortTy typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfWhy) with (equivDataTypes typeA typeB)
        validCast (PortTy typeA dirA) (PortTy typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfWhy) | (Yes prfTy) = Yes (CanCast prfWhy prfTy)
        validCast (PortTy typeA dirA) (PortTy typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (Yes prfWhy) | (No msgWhyNot prfWhyNot) = No (TypesNotEquiv msgWhyNot) (typeNotEquiv prfWhyNot)
      validCast (PortTy typeA dirA) (PortTy typeB dirB) | (Yes IsCastable) | (Yes IsCastable) | (No msgWhyNot prfWhyNot) = No (DirNotCast msgWhyNot) (dirNotCastable prfWhyNot)
    validCast (PortTy type dir) typeB | (Yes IsCastable) | (No contra) = No (NotCastableTo typeB) (cannotCastTo contra)
  validCast typeA typeB | (No contra) = No (NotCastableFrom typeA) (cannotCastFrom contra)
