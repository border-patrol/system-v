module SystemV.Params.Types.TYPE.Check.Data

import Decidable.Equality

import Toolkit.Decidable.Informative

import SystemV.Params.Types.TYPE

%default total

||| A predicate to type check data types against values
public export
data TyCheckData : (type  : TYPE (DATA TYPE))
                -> (value : TYPE (DATA TERM))
                -> Type
  where
    ChkData : TyCheckData DATATYPE DATATERM


public export
data Error = WrongType (TYPE (DATA TYPE)) (TYPE (DATA TERM))

--wrongType : (TyCheckData DATATYPE x -> Void)
--         -> TyCheckData DATATYPE (VectorTy x)
--         -> Void
--wrongType f (ChkDataVector y) = f y

export
typeCheck : (type  : TYPE (DATA TYPE))
         -> (value : TYPE (DATA TERM))
                  -> DecInfo Data.Error (TyCheckData type value)
typeCheck DATATYPE DATATERM = Yes ChkData

-- [ EOF ]
