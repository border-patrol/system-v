module SystemV.Params.Evaluation.Values.Predicates

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values

%default total

namespace Nat
  public export
  data IsNat : (term  : SystemV Nil (NatTy n))
            -> (value : Value term)
                     -> Type
    where
      ItIsPure : IsNat (MkNat n)
                       (MkNat)
      ItIsOver : IsNat (NatOverride m)
                       (NatOverride)

  isSeq : IsNat (Seq left right) (Seq x y) -> Void
  isSeq ItIsPure impossible
  isSeq ItIsOver impossible

  export
  isNat : {term  : SystemV Nil (NatTy n)}
       -> (value : Value term)
                -> Dec (IsNat term value)
  isNat MkNat = Yes ItIsPure
  isNat NatOverride = Yes ItIsOver
  isNat (Seq x y) = No isSeq

namespace Port
  public export
  data IsPort : (term  : SystemV Nil (PortTy datatype dir))
             -> (value : Value term)
                      -> Type
    where
      ItIs : IsPort (MkPort datatypeTerm  dir)
                    (MkPort datatypeValue dir)

  isSeq : IsPort (Seq left right) (Seq x y) -> Void
  isSeq ItIs impossible

  export
  isPort : {term  : SystemV Nil (PortTy datatype dir)}
        -> (value : Value term)
                 -> Dec (IsPort term value)
  isPort (MkPort x dir) = Yes ItIs
  isPort (Seq x y) = No isSeq

  public export
  PortIsNotSeq : (term  : SystemV Nil (PortTy datatype dir))
              -> (value : Value term)
                       -> Type
  PortIsNotSeq = IsPort

-- [ EOF ]
