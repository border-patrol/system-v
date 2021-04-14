||| Types in SystemV.Base.
|||
||| Types in SystemV.Base.are indexed over two levels:
|||
||| + TERM, that describes types that describe terms.
||| + TYPE, that describes types that describe types.
|||
module SystemV.Base.Types.TYPE

import public Toolkit.Data.Whole

import public SystemV.Common.Types.Direction

import public SystemV.Common.Types.Level
import public SystemV.Common.Types.Universe

%default total

||| Our types are meta types...
public export
data TYPE : Universe -> Type where
  -- [ Data types ]

  -- Type def.
  TypeDefTy : TYPE (DATA level) -> TYPE (DATA level)

  -- Primitive Types
  BoolTyDesc : TYPE (DATA TYPE)
  BoolTy     : TYPE (DATA TERM)

  LogicTyDesc : TYPE (DATA TYPE)
  LogicTy     : TYPE (DATA TERM)

  VectorTyDesc : (size : Whole)
              -> (type : TYPE (DATA TYPE))
                      -> TYPE (DATA TYPE)

  VectorTy : (size : Whole)
          -> (type : TYPE (DATA TERM))
                  -> TYPE (DATA TERM)

  -- [ Function types ]
  FuncTy : (param  : TYPE (IDX level))
        -> (return : TYPE (IDX level))
                  -> TYPE (IDX level)

  -- [ Structural Types ]

  -- Modules
  ModuleTyDesc : TYPE (IDX TYPE)
  ModuleTy     : TYPE (IDX TERM)

  -- Channels
  ChanTyDesc : (type : TYPE (DATA TYPE))
                    -> TYPE (IDX TYPE)

  ChanTy     : (type : TYPE (DATA TYPE))
                    -> TYPE (IDX TERM)

  PortTyDesc  : (type : TYPE (DATA TYPE))
             -> (dir  : Direction)
                     -> TYPE (IDX TYPE)

  PortTy : (type : TYPE (DATA TYPE))
        -> (dir  : Direction)
                -> TYPE (IDX TERM)

  -- [ Misc ]
  UnitTyDesc : TYPE (IDX TYPE)
  UnitTy     : TYPE (IDX TERM)

  NatTyDesc : Nat -> TYPE (IDX TYPE)
  NatTy     : Nat -> TYPE (IDX TERM)




-- --------------------------------------------------------------------- [ EOF ]
