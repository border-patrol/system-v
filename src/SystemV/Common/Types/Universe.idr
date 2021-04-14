module SystemV.Common.Types.Universe

import Decidable.Equality

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
DecEq Universe where
  decEq (DATA x) (DATA y) with (decEq x y)
    decEq (DATA x) (DATA x) | (Yes Refl) = Yes Refl
    decEq (DATA x) (DATA y) | (No contra) = No (dataNotSameLevel contra)

  decEq (DATA x) (IDX y) = No dataIdxNotEq

  decEq (IDX x) (DATA y) = No (negEqSym dataIdxNotEq)
  decEq (IDX x) (IDX y) with (decEq x y)
    decEq (IDX x) (IDX x) | (Yes Refl) = Yes Refl
    decEq (IDX x) (IDX y) | (No contra) = No (idxNotSameLevel contra)

-- [ EOF ]
