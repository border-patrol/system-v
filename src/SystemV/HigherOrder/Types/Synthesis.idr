module SystemV.HigherOrder.Types.Synthesis

import Decidable.Equality

import Data.Vect
import Data.List
import Data.List.Views
import Data.String
import Data.Maybe

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Core.Types.TYPE
import SystemV.Core.Types.TYPE.Check.Types

import SystemV.HigherOrder.Types.Function

%default total

namespace Argument
  public export
  data Synthesis : (type : TYPE (IDX TYPE))
                -> (term : TYPE (IDX TERM))
                        -> Type
    where
      Synth : (term : TYPE (IDX TERM))
           -> Argument.Type.Valid (IDX TYPE) type
           -> Argument.Term.Valid (IDX TERM)      term
           -> TyCheck                        type term
           -> Synthesis                      type term


  public export
  data Error = NotValidArgumentType Argument.Type.Error

namespace Returned
  public export
  data Synthesis : (type : TYPE (IDX TYPE))
                -> (term : TYPE (IDX TERM))
                        -> Type
    where
      Synth : (term : TYPE (IDX TERM))
           -> Returned.Type.Valid (IDX TYPE) type
           -> Returned.Term.Valid (IDX TERM)      term
           -> TyCheck                        type term
           -> Synthesis                      type term


notValidArgumentType : (Argument.Type.Valid (IDX TYPE) type -> Void)
                    -> (term : TYPE (IDX TERM) ** Argument.Synthesis type term)
                            -> Void
notValidArgumentType f (MkDPair fst (Synth fst x y z)) = f x

mutual
  doSynthRet : (type : TYPE (IDX TYPE))
            -> (prf  : Returned.Type.Valid (IDX TYPE) type)
                    -> (term : TYPE (IDX TERM) ** Returned.Synthesis type term)
  doSynthRet ModuleTyDesc IsModuleTyDesc
    = (ModuleTy ** Synth ModuleTy
                         IsModuleTyDesc
                         IsModuleTy
                         ChkModule)

  doSynthRet (FuncTy param return) (IsFuncTyDesc (IsFuncTyDesc x y))
    = let (pTm ** Synth pTm prfTyP prfTmP pChk) = doSynthArg param  x in
      let (rTm ** Synth rTm prfTyR prfTmR rChk) = doSynthRet return y
       in (FuncTy pTm rTm ** Synth (FuncTy pTm rTm)
                                   (IsFuncTyDesc (IsFuncTyDesc x y))
                                   (IsFuncTy (IsFuncTy prfTmP prfTmR))
                                   (ChkFunc pChk rChk))

  doSynthArg : (type : TYPE (IDX TYPE))
            -> (prf  : Argument.Type.Valid (IDX TYPE) type)
                   -> (term : TYPE (IDX TERM) ** Argument.Synthesis type term)

  doSynthArg (PortTyDesc type dir) IsPortTyDesc
    = (PortTy type dir ** Synth (PortTy type dir)
                                IsPortTyDesc
                                IsPortTy
                                (ChkPort (Same Refl Refl) Refl))

  doSynthArg UnitTyDesc IsUnitTyDesc
    = (UnitTy ** Synth UnitTy
                       IsUnitTyDesc
                       IsUnitTy
                       ChkUnit)

  doSynthArg (FuncTy param return) (IsFuncTyDesc (IsFuncTyDesc x y))
    = let (pTm ** Synth pTm prfTyP prfTmP pChk) = doSynthArg param  x in
      let (rTm ** Synth rTm prfTyR prfTmR rChk) = doSynthRet return y
       in (FuncTy pTm rTm ** Synth (FuncTy pTm rTm)
                                   (IsFuncTyDesc (IsFuncTyDesc x y))
                                   (IsFuncTy (IsFuncTy prfTmP prfTmR))
                                   (ChkFunc pChk rChk))

export
synthesis : (type : TYPE (IDX TYPE))
         -> DecInfo Synthesis.Argument.Error
                    (term : TYPE (IDX TERM) ** Argument.Synthesis type term)
synthesis type with (Argument.Type.valid (IDX TYPE) type)
  synthesis type | (Yes prfWhy) with (doSynthArg type prfWhy)
    synthesis type | (Yes prfWhy) | (term ** synth)
      = Yes (term ** synth)

  synthesis type | (No msgWhyNot prfWhyNot)
    = No (NotValidArgumentType msgWhyNot) (notValidArgumentType prfWhyNot)


-- [ EOF ]
