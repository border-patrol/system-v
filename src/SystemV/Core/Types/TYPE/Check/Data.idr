module SystemV.Core.Types.TYPE.Check.Data

import Decidable.Equality

import Toolkit.Decidable.Informative

import SystemV.Core.Types.TYPE

%default total

||| A predicate to type check data types against values
public export
data TyCheckData : (type  : TYPE (DATA TYPE))
                -> (value : TYPE (DATA TERM))
                -> Type
  where
    ChkDataLogic  : TyCheckData LogicTyDesc LogicTy

    ChkDataVector : (prf : s = t)
                 -> TyCheckData                 typeDesc              type
                 -> TyCheckData (VectorTyDesc s typeDesc) (VectorTy t type)

public export
data Error = WrongType (TYPE (DATA TYPE)) (TYPE (DATA TERM))

vectIsNotLogic : TyCheckData LogicTyDesc (VectorTy n x) -> Void
vectIsNotLogic ChkDataLogic impossible
vectIsNotLogic (ChkDataVector p y) impossible

logicIsNotVect : TyCheckData (VectorTyDesc n x) (LogicTy) -> Void
logicIsNotVect ChkDataLogic impossible
logicIsNotVect (ChkDataVector p y) impossible

vectorWrongSize : (contra : n === k -> Void)
               -> (prf    : TyCheckData (VectorTyDesc n x) (VectorTy k y))
                         -> Void
vectorWrongSize contra (ChkDataVector Refl z) = contra Refl

vectorWrongType : (contra : TyCheckData x y -> Void)
               -> (prf    : TyCheckData (VectorTyDesc n x) (VectorTy k y))
                         -> Void
vectorWrongType contra (ChkDataVector Refl z) = contra z

export
typeCheck : (type  : TYPE (DATA TYPE))
         -> (value : TYPE (DATA TERM))
                  -> DecInfo Data.Error (TyCheckData type value)

typeCheck LogicTyDesc value with (value)
  typeCheck LogicTyDesc value | LogicTy
    = Yes ChkDataLogic
  typeCheck LogicTyDesc value | (VectorTy n x)
    = No (WrongType LogicTyDesc value) vectIsNotLogic

typeCheck (VectorTyDesc n x) value with (value)
  typeCheck (VectorTyDesc n x) value | LogicTy
    = No (WrongType (VectorTyDesc n x) value) logicIsNotVect
  typeCheck (VectorTyDesc n x) value | (VectorTy k y) with (decEq n k)
    typeCheck (VectorTyDesc k x) value | (VectorTy k y) | (Yes Refl) with (typeCheck x y)
      typeCheck (VectorTyDesc k x) value | (VectorTy k y) | (Yes Refl) | (Yes prfWhy)
        = Yes (ChkDataVector Refl prfWhy)
      typeCheck (VectorTyDesc k x) value | (VectorTy k y) | (Yes Refl) | (No msgWhyNot prfWhyNot)
        = No (WrongType (VectorTyDesc k x) value) (vectorWrongType prfWhyNot)
    typeCheck (VectorTyDesc n x) value | (VectorTy k y) | (No contra)
      = No (WrongType (VectorTyDesc n x) value) (vectorWrongSize contra)
