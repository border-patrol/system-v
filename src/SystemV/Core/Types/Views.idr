module SystemV.Core.Types.Views

import Decidable.Equality

import Toolkit.Decidable.Informative
import Toolkit.Decidable.Equality.Indexed

import SystemV.Common.Utilities

import SystemV.Core.Types

%default total


namespace AllDataEqual
  public export
  data Error = AB | AC

  public export
  data AllDataEqual : (a,b,c : TYPE (DATA TYPE)) -> Type where
    ADE : AllDataEqual a a a

  abNotEqual : {a,b : _} -> (Equals Universe TYPE a b -> Void) -> AllDataEqual a b c -> Void
  abNotEqual f ADE = f (Same Refl Refl)

  acNotEqual : {a,b,c : _} -> (Equals Universe TYPE b c -> Void) -> AllDataEqual a b c -> Void
  acNotEqual f ADE = f (Same Refl Refl)

  export
  allDataEqual : (a,b,c : TYPE (DATA TYPE)) -> DecInfo AllDataEqual.Error (AllDataEqual a b c)
  allDataEqual a b c with (DataTypes.decEq a b)
    allDataEqual a b c | (Yes prfAB) with (DataTypes.decEq b c)
      allDataEqual a b c | (Yes prfAB) | (Yes prfBC) with (Indexed.trans prfAB prfBC)
        allDataEqual c c c | (Yes (Same Refl Refl)) | (Yes (Same Refl Refl)) | (Same Refl Refl)
          = Yes ADE
      allDataEqual a b c | (Yes prfAB) | (No msgWhyNot prfWhyNot)
        = No AC (acNotEqual prfWhyNot)
    allDataEqual a b c | (No msgWhyNot prfWhyNot)
      = No AB (abNotEqual prfWhyNot)

namespace HasDirection
  public export
  data HasDirection : (d : Direction) -> (u : Universe) -> (type : TYPE u) -> Type where
     Match : (prf : da === db)
                 -> HasDirection da (IDX TERM) (PortTy ty db)
     Fail  : (contra : Not (da === db))
                    -> HasDirection da (IDX TERM) (PortTy ty db)
     NotAPort : HasDirection da u type


  export
  hasDirection : (d : Direction) -> (u : Universe) -> (type : TYPE u) -> HasDirection d u type
  hasDirection d (IDX TERM) (PortTy type dir) with (Direction.decEq d dir)
    hasDirection d (IDX TERM) (PortTy type dir) | (Yes prf)
      = Match prf
    hasDirection d (IDX TERM) (PortTy type dir) | (No contra)
      = Fail contra

  hasDirection d _ _ = NotAPort

namespace IsPort
  public export
  data IsPort : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsPort (IDX TERM) (PortTy ty dir)
    Fail  : IsPort u type

  export
  isPort : (u : Universe) -> (type : TYPE u) -> IsPort u type
  isPort (IDX TERM) (PortTy type dir) = Match
  isPort _ _ = Fail

namespace IsUnit
  public export
  data IsUnit : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsUnit (IDX TERM) UnitTy
    Fail  : IsUnit u type

  export
  isUnit : (u : Universe) -> (type : TYPE u) -> IsUnit u type
  isUnit (IDX TERM) UnitTy = Match
  isUnit _ _ = Fail

namespace IsChan
  public export
  data IsChan : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsChan (IDX TERM) (ChanTy type)
    Fail  : IsChan u type

  export
  isChan : (u : Universe) -> (type : TYPE u) -> IsChan u type
  isChan (IDX TERM) (ChanTy type) = Match
  isChan _ _ = Fail

namespace IsData
  public export
  data IsData : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsData (DATA TYPE) type
    Fail  : IsData u type

  export
  isData : (u : Universe) -> (type : TYPE u) -> IsData u type
  isData (DATA TYPE) _ = Match
  isData _ _ = Fail

namespace IsTerm
  public export
  data IsTerm : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsTerm (IDX level) type
    Fail  : IsTerm u type

  export
  isTerm : (u : Universe) -> (type : TYPE u) -> IsTerm u type
  isTerm (IDX level) _ = Match
  isTerm _ _ = Fail

namespace IsType
  public export
  data IsType : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsType (IDX TYPE) type
    Fail  : IsType u type

  export
  isType : (u : Universe) -> (type : TYPE u) -> IsType u type
  isType (IDX TYPE) _ = Match
  isType _ _ = Fail

namespace IsPortTy
  public export
  data IsPortTy : (u : Universe) -> (type : TYPE u) -> Type where
    Match : IsPortTy (IDX TYPE) (PortTyDesc d dir)
    Fail  : IsPortTy u type

  export
  isPortTy : (u : Universe) -> (type : TYPE u) -> IsPortTy u type
  isPortTy (IDX TYPE) (PortTyDesc d dir) = Match
  isPortTy _ _ = Fail

namespace IsPortVect
  public export
  data IsPortVect : (u : Universe) -> (type : TYPE u) -> Type where
    Match    : IsPortVect (IDX TERM) (PortTy (VectorTyDesc s ty) dir)
    Fail     : IsPortVect (IDX TERM) (PortTy ty dir)
    NotAPort : IsPortVect u          type

  export
  isPortVect : (u : Universe) -> (type : TYPE u) -> IsPortVect u type
  isPortVect (IDX TERM) (PortTy (VectorTyDesc size type) dir) = Match
  isPortVect (IDX TERM) (PortTy LogicTyDesc dir) = Fail
  isPortVect _ _ = NotAPort

namespace IsFuncTy
  public export
  data IsFuncTy : (u : Universe) -> (type : TYPE u) -> Type where
    Match    : IsFuncTy (IDX TYPE) (FuncTy a b)
    WrongTm  : IsFuncTy (IDX _)    type
    NotATerm : IsFuncTy u          type

  export
  isFuncTy : (u : Universe) -> (type : TYPE u) -> IsFuncTy u type
  isFuncTy (IDX TYPE) (FuncTy a b) = Match
  isFuncTy (IDX _) _ = WrongTm
  isFuncTy _ _ = NotATerm

namespace IsFunc
  public export
  data IsFunc : (u : Universe) -> (type : TYPE u) -> Type where
    Match    : IsFunc (IDX TERM) (FuncTy a b)
    WrongTm  : IsFunc (IDX _)    type
    NotATerm : IsFunc u          type

  export
  isFunc : (u : Universe) -> (type : TYPE u) -> IsFunc u type
  isFunc (IDX TERM) (FuncTy a b) = Match
  isFunc (IDX _) _ = WrongTm
  isFunc _ _ = NotATerm


-- [ EoF ]
