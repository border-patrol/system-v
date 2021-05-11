module SystemV.Param.Types.TYPE.Check.Data

import Decidable.Equality

import Toolkit.Decidable.Informative

import SystemV.Param.Types.TYPE

%default total

||| A predicate to type check data types against values
public export
data TyCheckData : (type  : TYPE (DATA TYPE))
                -> (value : TYPE (DATA TERM))
                -> Type
  where
    ChkDataLogic  : TyCheckData DATATYPE LogicTy

    ChkDataVector : TyCheckData DATATYPE           type
                 -> TyCheckData DATATYPE (VectorTy type)

public export
data Error = WrongType (TYPE (DATA TYPE)) (TYPE (DATA TERM))

wrongType : (TyCheckData DATATYPE x -> Void)
         -> TyCheckData DATATYPE (VectorTy x)
         -> Void
wrongType f (ChkDataVector y) = f y

export
typeCheck : (type  : TYPE (DATA TYPE))
         -> (value : TYPE (DATA TERM))
                  -> DecInfo Data.Error (TyCheckData type value)
typeCheck DATATYPE LogicTy = Yes ChkDataLogic
typeCheck DATATYPE (VectorTy x) with (typeCheck DATATYPE x)
  typeCheck DATATYPE (VectorTy x) | (Yes prfWhy) = Yes (ChkDataVector prfWhy)
  typeCheck DATATYPE (VectorTy x) | (No msgWhyNot prfWhyNot)
    = No (WrongType DATATYPE (VectorTy x)) (wrongType prfWhyNot)

{-

vectIsNotLogic : TyCheckData LogicTyDesc (VectorTy x) -> Void
vectIsNotLogic ChkDataLogic impossible
vectIsNotLogic (ChkDataVector y) impossible

logicIsNotVect : TyCheckData (VectorTyDesc x) (LogicTy) -> Void
logicIsNotVect ChkDataLogic impossible
logicIsNotVect (ChkDataVector y) impossible

vectorWrongType : (contra : TyCheckData x y -> Void)
               -> (prf    : TyCheckData (VectorTyDesc x) (VectorTy y))
                         -> Void
vectorWrongType contra (ChkDataVector z) = contra z

export
typeCheck : (type  : TYPE (DATA TYPE))
         -> (value : TYPE (DATA TERM))
                  -> DecInfo Data.Error (TyCheckData type value)
typeCheck LogicTyDesc value with (value)
  typeCheck LogicTyDesc value | LogicTy
    = Yes ChkDataLogic
  typeCheck LogicTyDesc value | (VectorTy x)
    = No (WrongType LogicTyDesc value) vectIsNotLogic

typeCheck (VectorTyDesc x) value with (value)
  typeCheck (VectorTyDesc x) value | LogicTy
    = No (WrongType (VectorTyDesc x) value) logicIsNotVect
  typeCheck (VectorTyDesc x) value | (VectorTy y) with (typeCheck x y)
    typeCheck (VectorTyDesc x) value | (VectorTy y) | (Yes prfWhy)
      = Yes (ChkDataVector prfWhy)
    typeCheck (VectorTyDesc x) value | (VectorTy y) | (No msgWhyNot prfWhyNot)
      = No (WrongType (VectorTyDesc x) value) (vectorWrongType prfWhyNot)
-}
