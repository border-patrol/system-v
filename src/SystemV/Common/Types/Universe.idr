module SystemV.Common.Types.Universe

import Decidable.Equality
import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Types.Level

%default total

||| The Universes in our setup: Data or things that contain data.
public export
data Universe = DATA Level -- Describes things that are data.
              | IDX  Level -- Describes things that contain data.


dataNotSameLevel : (contra : x = y -> Void)
                -> (prf    : DATA x = DATA y)
                          -> Void
dataNotSameLevel contra Refl = contra Refl

dataIdxNotEq : DATA x = IDX y -> Void
dataIdxNotEq Refl impossible

idxNotSameLevel : (contra : x = y -> Void)
               -> (prf    : IDX x = IDX y)
                         -> Void
idxNotSameLevel contra Refl = contra Refl

export
decEq : (a,b : Universe)
            -> Dec (a === b)
decEq (DATA x) (DATA y) with (decEq x y)
  decEq (DATA x) (DATA x) | (Yes Refl) = Yes Refl
  decEq (DATA x) (DATA y) | (No contra) = No (dataNotSameLevel contra)

decEq (DATA x) (IDX y) = No dataIdxNotEq


decEq (IDX x) (DATA y) = No (negEqSym dataIdxNotEq)
decEq (IDX x) (IDX y) with (decEq x y)
  decEq (IDX x) (IDX x) | (Yes Refl) = Yes Refl
  decEq (IDX x) (IDX y) | (No contra) = No (idxNotSameLevel contra)

export
DecEq Universe where
  decEq = Universe.decEq


public export
data Error = SameLevels Universe
           | DiffUniverse Universe Universe
           | TypesMustType
           | ValuesMustValue

public export
data HasLevel : Level -> Universe -> Type where
  HasLvlData : HasLevel u (DATA u)
  HasLvlIdx  : HasLevel u (IDX  u)

dataIsType : HasLevel TERM (DATA TYPE) -> Void
dataIsType HasLvlData impossible

idxIsType : HasLevel TERM (IDX TYPE) -> Void
idxIsType HasLvlData impossible

dataIsTerm : HasLevel TYPE (DATA TERM) -> Void
dataIsTerm HasLvlData impossible

idxIsTerm : HasLevel TYPE (IDX TERM) -> Void
idxIsTerm HasLvlData impossible

export
hasLevel : (l : Level)
        -> (u : Universe)
             -> Dec (HasLevel l u)
hasLevel TERM (DATA TERM) = Yes HasLvlData
hasLevel TERM (DATA TYPE) = No dataIsType
hasLevel TERM (IDX TERM) = Yes HasLvlIdx
hasLevel TERM (IDX TYPE) = No idxIsType

hasLevel TYPE (DATA TERM) = No dataIsTerm
hasLevel TYPE (DATA TYPE) = Yes HasLvlData
hasLevel TYPE (IDX TERM) = No idxIsTerm
hasLevel TYPE (IDX TYPE) = Yes HasLvlIdx

public export
data SameUniverse : (typeLevel, valueLevel : Universe)
                 -> Type
  where
    DataU : SameUniverse (DATA x) (DATA y)
    IdxU  : SameUniverse (IDX x)  (IDX y)

diffUniverseDI : SameUniverse (DATA x) (IDX y) -> Void
diffUniverseDI DataU impossible

diffUniverseID : SameUniverse (IDX x) (DATA y) -> Void
diffUniverseID DataU impossible


export
sameUniverse : (typeLevel, valueLevel : Universe)
                                     -> DecInfo Error
                                                (SameUniverse typeLevel valueLevel)
sameUniverse (DATA x) (DATA y) = Yes DataU
sameUniverse (DATA x) (IDX y) = No (DiffUniverse (DATA x) (IDX y)) diffUniverseDI
sameUniverse (IDX x) (DATA y) = No (DiffUniverse (IDX y) (DATA x)) diffUniverseID
sameUniverse (IDX x) (IDX y) = Yes IdxU

public export
data ValidLevels : (typeLevel, valueLevel : Universe)
                                         -> Type
  where
    ForNat  : ValidLevels (IDX TYPE)  (IDX TERM)
    ForData : ValidLevels (DATA TYPE) (DATA TERM)


levelsSame : ValidLevels val val -> Void
levelsSame ForNat impossible

notSameU : (SameUniverse ty val -> Void) -> ValidLevels ty val -> Void
notSameU f ForNat = f IdxU
notSameU f ForData = f DataU

notType : (HasLevel TYPE ty -> Void) -> ValidLevels ty val -> Void
notType f ForNat = f HasLvlIdx
notType f ForData = f HasLvlData

notValue : (HasLevel TERM val -> Void) -> ValidLevels ty val -> Void
notValue f ForNat = f HasLvlIdx
notValue f ForData = f HasLvlData

export
validLevels : (typeLevel, valueLevel : Universe)
                                    -> DecInfo Error
                                                (ValidLevels typeLevel valueLevel)
validLevels ty val with (Universe.decEq ty val)
  validLevels val val | (Yes Refl)
    = No (SameLevels val) levelsSame
  validLevels ty val | (No contra) with (sameUniverse ty val)
    validLevels ty val | (No contra) | (Yes prfWhySameU) with (hasLevel TYPE ty)
      validLevels ty val | (No contra) | (Yes prfWhySameU) | (Yes prfTy) with (hasLevel TERM val)
        validLevels (DATA TYPE) (DATA TERM) | (No contra) | (Yes DataU) | (Yes HasLvlData) | (Yes HasLvlData)
          = Yes ForData
        validLevels (IDX TYPE) (IDX TERM) | (No contra) | (Yes IdxU) | (Yes HasLvlIdx) | (Yes HasLvlIdx)
          = Yes ForNat

        validLevels ty val | (No contra) | (Yes prfWhySameU) | (Yes prfTy) | (No f)
          = No ValuesMustValue (notValue f)

      validLevels ty val | (No contra) | (Yes prfWhySameU) | (No f)
        = No TypesMustType (notType f)
    validLevels ty val | (No contra) | (No msgWhyNot prfWhyNot)
      = No msgWhyNot (notSameU prfWhyNot)
-- [ EOF ]
