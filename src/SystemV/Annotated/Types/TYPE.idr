||| Types in SystemV.Base.
|||
||| Types in SystemV.Base.are indexed over two levels:
|||
||| + TERM, that describes types that describe terms.
||| + TYPE, that describes types that describe types.
|||
module SystemV.Annotated.Types.TYPE

import public Toolkit.Data.Whole

import public SystemV.Common.Types.Direction

import public SystemV.Common.Types.Level
import public SystemV.Common.Types.Universe

import public SystemV.Annotated.Types.Sensitivity
import public SystemV.Annotated.Types.Intention

%default total

namespace Core
  ||| Our types are meta types...
  public export
  data TYPE : Universe -> Type where
    -- [ Data types ]

    -- Primitive Types
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
              -> (sens : Sensitivity)
              -> (inte : Intention)
                      -> TYPE (IDX TYPE)

    ChanTy     : (type : TYPE (DATA TYPE))
              -> (sens : Sensitivity)
              -> (inte : Intention)
                      -> TYPE (IDX TERM)

    PortTyDesc  : (type : TYPE (DATA TYPE))
               -> (dir  : Direction)
               -> (sens : Sensitivity)
               -> (inte : Intention)
                       -> TYPE (IDX TYPE)

    PortTy : (type : TYPE (DATA TYPE))
          -> (dir  : Direction)
          -> (sens : Sensitivity)
          -> (inte : Intention)
                  -> TYPE (IDX TERM)

    -- [ Misc ]
    UnitTyDesc : TYPE (IDX TYPE)
    UnitTy     : TYPE (IDX TERM)

-- --------------------------------------------------------------------- [ EOF ]
