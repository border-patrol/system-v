module SystemV.Core.Types.TYPE.Function.Synthesis

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.Strings
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Core.Types.TYPE
import SystemV.Core.Types.TYPE.Check.Types
import SystemV.Core.Types.TYPE.Function.Argument


%default total

public export
data Synthesis : (type : TYPE (IDX TYPE))
              -> (term : TYPE (IDX TERM))
                      -> Type
  where
    Synth : (term : TYPE (IDX TERM))
         -> Argument.ValidType (IDX TYPE) type
         -> Argument.ValidTerm (IDX TERM)      term
         -> TyCheck                       type term
         -> Synthesis                     type term

public export
data Error = NotValidArgumentType Argument.ValidType.Error

notValidArgumentType : (ValidType (IDX TYPE) type -> Void)
                    -> (term : TYPE (IDX TERM) ** Synthesis type term)
                            -> Void
notValidArgumentType f (MkDPair fst (Synth fst x y z)) = f x

export
synthesis : (type : TYPE (IDX TYPE))
         -> DecInfo Synthesis.Error
                    (term : TYPE (IDX TERM) ** Synthesis type term)
synthesis type with (validType (IDX TYPE) type)
  synthesis (PortTyDesc type dir) | (Yes IsPortTyDesc)
    = Yes (PortTy type dir ** Synth (PortTy type dir)
                                    IsPortTyDesc
                                    IsPortTy
                                    (ChkPort (Same Refl Refl)
                                             Refl))

  synthesis UnitTyDesc | (Yes IsUnitTyDesc)
    = Yes (UnitTy ** Synth UnitTy IsUnitTyDesc IsUnitTy ChkUnit)

  synthesis type | (No msgWhyNot prfWhyNot)
    = No (NotValidArgumentType msgWhyNot) (notValidArgumentType prfWhyNot)

-- [ EOF ]
