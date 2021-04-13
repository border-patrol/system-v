module SystemV.Types.TYPE.Check.Data

import Decidable.Equality

import Toolkit.Decidable.Informative

import SystemV.Utilities

import public SystemV.Types.Direction
import public SystemV.Types.TYPE

%default total

||| A predicate to type check data types against values
public export
data TyCheckData : (type  : TYPE (DATA TYPE))
                -> (value : TYPE (DATA TERM))
                -> Type
  where
    ChkDataBool   : TyCheckData BoolTyDesc  BoolTy
    ChkDataLogic  : TyCheckData LogicTyDesc LogicTy

    ChkDataVector : (prf : s = t)
                 -> TyCheckData                 typeDesc              type
                 -> TyCheckData (VectorTyDesc s typeDesc) (VectorTy t type)

    ChkNewtype   : TyCheckData            innerType             innerValue
                -> TyCheckData (TypeDefTy innerType) (TypeDefTy innerValue)

public export
data Error = WrongType (TYPE (DATA TYPE)) (TYPE (DATA TERM))


boolIsNotTypeDef : TyCheckData (TypeDefTy x) BoolTy -> Void
boolIsNotTypeDef ChkDataBool impossible
boolIsNotTypeDef ChkDataLogic impossible
boolIsNotTypeDef (ChkDataVector p y) impossible
boolIsNotTypeDef (ChkNewtype y) impossible

logicIsNotTypeDef : TyCheckData (TypeDefTy x) LogicTy -> Void
logicIsNotTypeDef ChkDataBool impossible
logicIsNotTypeDef ChkDataLogic impossible
logicIsNotTypeDef (ChkDataVector p y) impossible
logicIsNotTypeDef (ChkNewtype y) impossible

vectIsNotTypeDef : TyCheckData (TypeDefTy x) (VectorTy n y) -> Void
vectIsNotTypeDef ChkDataBool impossible
vectIsNotTypeDef ChkDataLogic impossible
vectIsNotTypeDef (ChkDataVector prf z) impossible
vectIsNotTypeDef (ChkNewtype z) impossible

wrongInner : (contra : TyCheckData tyI valI -> Void)
          -> (prf    : TyCheckData (TypeDefTy tyI) (TypeDefTy valI))
                    -> Void
wrongInner contra (ChkNewtype x) = contra x

typeDefIsNotBool : TyCheckData BoolTyDesc (TypeDefTy x) -> Void
typeDefIsNotBool ChkDataBool impossible
typeDefIsNotBool ChkDataLogic impossible
typeDefIsNotBool (ChkDataVector p y) impossible
typeDefIsNotBool (ChkNewtype y) impossible

logicIsNotBool : TyCheckData BoolTyDesc LogicTy -> Void
logicIsNotBool ChkDataBool impossible
logicIsNotBool ChkDataLogic impossible
logicIsNotBool (ChkDataVector p y) impossible
logicIsNotBool (ChkNewtype x) impossible

vectIsNotBool : TyCheckData BoolTyDesc (VectorTy n x) -> Void
vectIsNotBool ChkDataBool impossible
vectIsNotBool ChkDataLogic impossible
vectIsNotBool (ChkDataVector p y) impossible
vectIsNotBool (ChkNewtype y) impossible

typeDefIsNotLogic : TyCheckData LogicTyDesc (TypeDefTy x) -> Void
typeDefIsNotLogic ChkDataBool impossible
typeDefIsNotLogic ChkDataLogic impossible
typeDefIsNotLogic (ChkDataVector p y) impossible
typeDefIsNotLogic (ChkNewtype y) impossible

boolIsNotLogic : TyCheckData LogicTyDesc BoolTy -> Void
boolIsNotLogic ChkDataBool impossible
boolIsNotLogic ChkDataLogic impossible
boolIsNotLogic (ChkDataVector p y) impossible
boolIsNotLogic (ChkNewtype x) impossible

vectIsNotLogic : TyCheckData LogicTyDesc (VectorTy n x) -> Void
vectIsNotLogic ChkDataBool impossible
vectIsNotLogic ChkDataLogic impossible
vectIsNotLogic (ChkDataVector p y) impossible
vectIsNotLogic (ChkNewtype y) impossible

typeDefIsNotVect : TyCheckData (VectorTyDesc n x) (TypeDefTy i) -> Void
typeDefIsNotVect ChkDataBool impossible
typeDefIsNotVect ChkDataLogic impossible
typeDefIsNotVect (ChkDataVector p y) impossible
typeDefIsNotVect (ChkNewtype y) impossible

boolIsNotVect : TyCheckData (VectorTyDesc n x) (BoolTy) -> Void
boolIsNotVect ChkDataBool impossible
boolIsNotVect ChkDataLogic impossible
boolIsNotVect (ChkDataVector p y) impossible
boolIsNotVect (ChkNewtype y) impossible

logicIsNotVect : TyCheckData (VectorTyDesc n x) (LogicTy) -> Void
logicIsNotVect ChkDataBool impossible
logicIsNotVect ChkDataLogic impossible
logicIsNotVect (ChkDataVector p y) impossible
logicIsNotVect (ChkNewtype y) impossible

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
typeCheck (TypeDefTy x) value with (value)
  typeCheck (TypeDefTy x) value | (TypeDefTy y) with (typeCheck x y)
    typeCheck (TypeDefTy x) value | (TypeDefTy y) | (Yes prfWhy)
      = Yes (ChkNewtype prfWhy)
    typeCheck (TypeDefTy x) value | (TypeDefTy y) | (No msgWhyNot prfWhyNot)
      = No msgWhyNot (wrongInner prfWhyNot)

  typeCheck (TypeDefTy x) value | BoolTy
    = No (WrongType (TypeDefTy x) value) boolIsNotTypeDef
  typeCheck (TypeDefTy x) value | LogicTy
    =  No (WrongType (TypeDefTy x) value) logicIsNotTypeDef
  typeCheck (TypeDefTy x) value | (VectorTy n y)
    = No (WrongType (TypeDefTy x) value) vectIsNotTypeDef

typeCheck BoolTyDesc value with (value)
  typeCheck BoolTyDesc value | (TypeDefTy x)
    = No (WrongType BoolTyDesc value) typeDefIsNotBool
  typeCheck BoolTyDesc value | BoolTy
    = Yes ChkDataBool
  typeCheck BoolTyDesc value | LogicTy
    = No (WrongType BoolTyDesc value) logicIsNotBool
  typeCheck BoolTyDesc value | (VectorTy n x)
    = No (WrongType BoolTyDesc value) vectIsNotBool

typeCheck LogicTyDesc value with (value)
  typeCheck LogicTyDesc value | (TypeDefTy x)
    = No (WrongType LogicTyDesc value) typeDefIsNotLogic
  typeCheck LogicTyDesc value | BoolTy
    = No (WrongType LogicTyDesc value) boolIsNotLogic
  typeCheck LogicTyDesc value | LogicTy
    = Yes ChkDataLogic
  typeCheck LogicTyDesc value | (VectorTy n x)
    = No (WrongType LogicTyDesc value) vectIsNotLogic

typeCheck (VectorTyDesc n x) value with (value)
  typeCheck (VectorTyDesc n x) value | (TypeDefTy y)
    = No (WrongType (VectorTyDesc n x) value) typeDefIsNotVect
  typeCheck (VectorTyDesc n x) value | BoolTy
    = No (WrongType (VectorTyDesc n x) value) boolIsNotVect
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
