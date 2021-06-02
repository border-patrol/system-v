||| Types in SystemV.Params.
|||
||| Types in SystemV.Params.are indexed over two levels:
|||
||| + TERM, that describes types that describe terms.
||| + TYPE, that describes types that describe types.
|||
module SystemV.Params.Types.TYPE

import public Toolkit.Data.Whole

import public SystemV.Common.Types.Direction

import public SystemV.Common.Types.Level
import public SystemV.Common.Types.Universe

%default total

namespace Params
  ||| Our types are meta types...
  public export
  data TYPE : Universe -> Type where
    -- [ Data types ]

    -- Primitive Types
    DATATYPE : TYPE (DATA TYPE)
    DATATERM : TYPE (DATA TERM)


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
    ChanTyDesc : TYPE (IDX TYPE)

    ChanTy :  TYPE (IDX TERM)

    PortTyDesc  : (dir  : Direction)
                       -> TYPE (IDX TYPE)

    PortTy : (dir  : Direction)
                  -> TYPE (IDX TERM)

    -- [ Misc ]
    UnitTyDesc : TYPE (IDX TYPE)
    UnitTy     : TYPE (IDX TERM)

    NatTyDesc : TYPE (IDX TYPE)
    NatTy     : TYPE (IDX TERM)

    BoolTyDesc : TYPE (IDX TYPE)
    BoolTy     : TYPE (IDX TERM)
-- --------------------------------------------------------------------- [ EOF ]
