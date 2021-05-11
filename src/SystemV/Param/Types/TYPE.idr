||| Types in SystemV.Param.
|||
||| Types in SystemV.Param.are indexed over two levels:
|||
||| + TERM, that describes types that describe terms.
||| + TYPE, that describes types that describe types.
|||
module SystemV.Param.Types.TYPE

import public Toolkit.Data.Whole

import public SystemV.Common.Types.Direction

import public SystemV.Common.Types.Level
import public SystemV.Common.Types.Universe

%default total

namespace Param
  ||| Our types are meta types...
  public export
  data TYPE : Universe -> Type where
    -- [ Data types ]

    -- Primitive Types
    DATATYPE : TYPE (DATA TYPE)
    LogicTy  : TYPE (DATA TERM)

    VectorTy : (type : TYPE (DATA TERM))
                    -> TYPE (DATA TERM)

    -- [ Function types ]
    FuncTy : (param  : TYPE (IDX level))
          -> (return : TYPE (IDX level))
                    -> TYPE (IDX level)

    FuncParamTy : (u   : Universe)
               -> (arg : TYPE u)
               -> (ret : TYPE (IDX level))
                      -> TYPE (IDX level)

    -- [ Structural Types ]

    -- Modules
    ModuleTyDesc : TYPE (IDX TYPE)
    ModuleTy     : TYPE (IDX TERM)

    -- Channels
    ChanTyDesc : (type : TYPE (DATA TERM))
                      -> TYPE (IDX TYPE)

    ChanTy     : (type : TYPE (DATA TERM))
                      -> TYPE (IDX TERM)

    PortTyDesc  : (type : TYPE (DATA TERM))
               -> (dir  : Direction)
                       -> TYPE (IDX TYPE)

    PortTy : (type : TYPE (DATA TERM))
          -> (dir  : Direction)
                  -> TYPE (IDX TERM)

    -- [ Misc ]
    UnitTyDesc : TYPE (IDX TYPE)
    UnitTy     : TYPE (IDX TERM)

    NatTyDesc : TYPE (IDX TYPE)
    NatTy     : TYPE (IDX TERM)

    BoolTyDesc : TYPE (IDX TYPE)
    BoolTy     : TYPE (IDX TERM)
-- --------------------------------------------------------------------- [ EOF ]
