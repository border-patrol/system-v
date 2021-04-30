module SystemV.Params.Evaluation.Slicing

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden
import SystemV.Params.Evaluation.Values.Predicates

%default total

public export
data Args : (portTm  : SystemV Nil (PortTy (VectorTyDesc s type) dir))
         -> (portVal : Value portTm)
         -> (alphaTm  : SystemV Nil (NatTy a))
         -> (alphaVal : Value alphaTm)
         -> (omegaTm  : SystemV Nil (NatTy o))
         -> (omegaVal : Value omegaTm)
                     -> Type
  where
    NoChange : ValidBound a o s
            -> Args (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyV) dir)
                    (MkNat a)                  MkNat
                    (MkNat o)                  MkNat

    OverPort : {ty   : SystemV Nil (VectorTyDesc s' typetype)}
            -> {tyV  : Value ty}
            -> (prfB : ValidBound a o s')
            -> (isV  : IsNotOverridden (VectorTyDesc s' typetype) ty tyV)
                    -> Args (MkPort (TyOverride ty) dir) (MkPort (TyOverride tyV) dir)
                            (MkNat a)                    MkNat
                            (MkNat o)                    MkNat

    OverPortA : {ty   : SystemV Nil (VectorTyDesc s' typetype)}
             -> {tyV  : Value ty}
             -> (prfB : ValidBound b o s')
             -> (isV  : IsNotOverridden (VectorTyDesc s' typetype) ty tyV)
                     -> Args (MkPort (TyOverride ty) dir) (MkPort (TyOverride tyV) dir)
                             (NatOverride b)              NatOverride
                             (MkNat o)                    MkNat

    OverPortO : {ty   : SystemV Nil (VectorTyDesc s' typetype)}
             -> {tyV  : Value ty}
             -> (prfB : ValidBound a m s')
             -> (isV  : IsNotOverridden (VectorTyDesc s' typetype) ty tyV)
                     -> Args (MkPort (TyOverride ty) dir) (MkPort (TyOverride tyV) dir)
                             (MkNat a)                    MkNat
                             (NatOverride m)              NatOverride

    OverPortAO : {ty   : SystemV Nil (VectorTyDesc s' typetype)}
              -> {tyV  : Value ty}
              -> (prfB : ValidBound b m s')
              -> (isV  : IsNotOverridden (VectorTyDesc s' typetype) ty tyV)
                      -> Args (MkPort (TyOverride ty) dir) (MkPort (TyOverride tyV) dir)
                              (NatOverride b)              NatOverride
                              (NatOverride m)              NatOverride

    OverA : ValidBound b o s
         -> Args (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyV) dir)
                 (NatOverride b)            NatOverride
                 (MkNat o)                  MkNat

    OverO : ValidBound a m s
         -> Args (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyV) dir)
                 (MkNat a)                  MkNat
                 (NatOverride m)            NatOverride

    OverAO : ValidBound b m s
          -> Args (MkPort (TyVect s ty) dir) (MkPort (TyVect s tyV) dir)
                  (NatOverride b)            NatOverride
                  (NatOverride m)            NatOverride

export
validArgs : (portTm   : SystemV Nil (PortTy (VectorTyDesc s type) dir))
         -> (portVal  : Value portTm)
         -> (alphaTm  : SystemV Nil (NatTy a))
         -> (alphaVal : Value alphaTm)
         -> (omegaTm  : SystemV Nil (NatTy o))
         -> (omegaVal : Value omegaTm)
                     -> Maybe (Args portTm  portVal
                                    alphaTm alphaVal
                                    omegaTm omegaVal)
-- @TODO Make cleaner with views
-- Check if port is sequence
validArgs pT pV aT aV oT oV with (isPort pV)
  -- Is port, and check if datatype overridden
  validArgs (MkPort dT dir) (MkPort dV dir) aT aV oT oV | (Yes ItIs) with (Alt.overridden dV)

    -- Yes port datatype overridden, but is the overridden type overridden
    validArgs (MkPort (TyOverride term) dir) (MkPort (TyOverride val) dir) aT aV oT oV | (Yes ItIs) | IsOver with (Alt.overridden val)

      -- Overridden port is a vector, move to check if Alpha a sequence or nat
      validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) aT aV oT oV | (Yes ItIs) | IsOver | IsVect with (isNat aV)

        -- Alpha is not a sequence, move to check omega
        validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat oT oV | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) with (isNat oV)

          -- Alpha is pure, so is omega
          validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (MkNat o) MkNat | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (Yes ItIsPure) with (validBound a o s')
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (MkNat o) MkNat | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (Yes ItIsPure) | (Yes prfWhy)
              = Just (OverPort prfWhy ItIsVect)
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (MkNat o) MkNat | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (Yes ItIsPure) | (No msgWhyNot prfWhyNot)
              = Nothing

          -- Omega is overridden
          validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (NatOverride m) NatOverride | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (Yes ItIsOver) with (validBound a m s')
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (NatOverride m) NatOverride | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (Yes ItIsOver) | (Yes prfWhy)
              = Just (OverPortO prfWhy ItIsVect)
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (NatOverride m) NatOverride | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (Yes ItIsOver) | (No msgWhyNot prfWhyNot)
              = Nothing

          -- Omega is a sequence
          validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat oT oV | (Yes ItIs) | IsOver | IsVect | (Yes ItIsPure) | (No contra)
            = Nothing

        -- Alpha is overridden
        validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride m) NatOverride oT oV | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) with (isNat oV)
          -- Omega is a Nat, check if overridden
          validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride m) NatOverride (MkNat o) MkNat | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (Yes ItIsPure) with (validBound m o s')
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride m) NatOverride (MkNat o) MkNat | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (Yes ItIsPure) | (Yes prfWhy)
              = Just (OverPortA prfWhy ItIsVect)
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride m) NatOverride (MkNat o) MkNat | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (Yes ItIsPure) | (No msgWhyNot prfWhyNot)
              = Nothing

          -- Omega is overridden
          validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (Yes ItIsOver) with (validBound b m s')
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (Yes ItIsOver) | (Yes prfWhy)
              = Just (OverPortAO prfWhy ItIsVect)
            validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (Yes ItIsOver) | (No msgWhyNot prfWhyNot)
              = Nothing

          -- Omega is a sequence.
          validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride m) NatOverride oT oV | (Yes ItIs) | IsOver | IsVect | (Yes ItIsOver) | (No contra)
            = Nothing


        -- Alpha is a Sequence, should not occur here...
        validArgs (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) aT aV oT oV | (Yes ItIs) | IsOver | IsVect | (No contra)
          = Nothing




      -- Double overrides are not allowed.
      validArgs (MkPort (TyOverride _) dir) (MkPort (TyOverride _) dir) aT aV oT oV | (Yes ItIs) | IsOver | alt
        = Nothing

    -- No port datatype is not
    validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) aT aV oT oV | (Yes ItIs) | IsVect with (isNat aV)
      validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat oT oV | (Yes ItIs) | IsVect | (Yes ItIsPure) with (isNat oV)
        validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat (MkNat o) MkNat | (Yes ItIs) | IsVect | (Yes ItIsPure) | (Yes ItIsPure) with (validBound a o s)
          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat (MkNat o) MkNat | (Yes ItIs) | IsVect | (Yes ItIsPure) | (Yes ItIsPure) | (Yes prfWhy)
            = Just (NoChange prfWhy)

          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat (MkNat o) MkNat | (Yes ItIs) | IsVect | (Yes ItIsPure) | (Yes ItIsPure) | (No msgWhyNot prfWhyNot)
            = Nothing -- Is Sequence

        validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat (NatOverride m) NatOverride | (Yes ItIs) | IsVect | (Yes ItIsPure) | (Yes ItIsOver) with (validBound a m s)
          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat (NatOverride m) NatOverride | (Yes ItIs) | IsVect | (Yes ItIsPure) | (Yes ItIsOver) | (Yes prfWhy)
            = Just (OverO prfWhy)
          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat (NatOverride m) NatOverride | (Yes ItIs) | IsVect | (Yes ItIsPure) | (Yes ItIsOver) | (No msgWhyNot prfWhyNot)
            = Nothing -- invalid bound

        validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (MkNat a) MkNat oT oV | (Yes ItIs) | IsVect | (Yes ItIsPure) | (No contra)
          = Nothing -- Is Sequence

      validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride oT oV | (Yes ItIs) | IsVect | (Yes ItIsOver) with (isNat oV)
        validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride (MkNat o) MkNat | (Yes ItIs) | IsVect | (Yes ItIsOver) | (Yes ItIsPure) with (validBound b o s)
          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride (MkNat o) MkNat | (Yes ItIs) | IsVect | (Yes ItIsOver) | (Yes ItIsPure) | (Yes prfWhy)
            = Just (OverA prfWhy)

          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride (MkNat o) MkNat | (Yes ItIs) | IsVect | (Yes ItIsOver) | (Yes ItIsPure) | (No msgWhyNot prfWhyNot)
            = Nothing -- invalid bound

        validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride | (Yes ItIs) | IsVect | (Yes ItIsOver) | (Yes ItIsOver) with (validBound b m s)
          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride | (Yes ItIs) | IsVect | (Yes ItIsOver) | (Yes ItIsOver) | (Yes prfWhy)
            = Just (OverAO prfWhy)

          validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride | (Yes ItIs) | IsVect | (Yes ItIsOver) | (Yes ItIsOver) | (No msgWhyNot prfWhyNot)
            = Nothing -- invalid bound

        validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) (NatOverride b) NatOverride oT oV | (Yes ItIs) | IsVect | (Yes ItIsOver) | (No contra)
          = Nothing -- Is Sequence

      validArgs (MkPort (TyVect s datatype) dir) (MkPort (TyVect s datatypev) dir) aT aV oT oV | (Yes ItIs) | IsVect | (No contra)
        = Nothing -- Is Sequence

  -- Is Sequence, should not occur here..
  validArgs pT pV aT aV oT oV | (No contra)
    = Nothing


public export
slice : {s : Whole}
     -> {a,o : Nat}
     -> {ty  : TYPE (DATA TYPE)}
     -> (portTm   : SystemV Nil (PortTy (VectorTyDesc s ty) dir))
     -> (portVal  : Value portTm)
     -> (alphaTm  : SystemV Nil (NatTy a))
     -> (alphaVal : Value alphaTm)
     -> (omegaTm  : SystemV Nil (NatTy o))
     -> (omegaVal : Value omegaTm)
     -> (prfOld   : ValidBound a o s)
     -> (prf      : Args portTm  portVal
                         alphaTm alphaVal
                         omegaTm omegaVal)
                 -> SystemV Nil (PortTy (VectorTyDesc (minus s o a prfOld) ty) dir)

slice {ty} portTm portVal alphaTm alphaVal omegaTm omegaVal prfOld prf with (prf)
  slice {ty = ty} (MkPort (TyVect s t) dir) (MkPort (TyVect s tyV) dir) (MkNat a) MkNat (MkNat o) MkNat prfOld prf | (NoChange x)
    = MkPort (TyVect (minus s o a prfOld) t) dir

  slice {ty = ty} (MkPort (TyOverride t) dir) (MkPort (TyOverride tyV) dir) (MkNat a) MkNat (MkNat o) MkNat prfOld prf | (OverPort prfB v) with (v)
    slice {ty = ty} (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (MkNat o) MkNat prfOld prf | (OverPort prfB v) | ItIsVect
      = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                           (TyVect (minus s' o a prfB) datatype))
               dir

  slice {ty = ty} (MkPort (TyOverride t) dir) (MkPort (TyOverride tyV) dir) (NatOverride b) NatOverride (MkNat o) MkNat prfOld prf | (OverPortA prfB v) with (v)
    slice {ty = ty} (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride b) NatOverride (MkNat o) MkNat prfOld prf | (OverPortA prfB v) | ItIsVect
      = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                           (TyVect (minus s' o b prfB) datatype))
               dir

  slice {ty = ty} (MkPort (TyOverride t) dir) (MkPort (TyOverride tyV) dir) (MkNat a) MkNat (NatOverride m) NatOverride prfOld prf | (OverPortO prfB v) with (v)
    slice {ty = ty} (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (MkNat a) MkNat (NatOverride m) NatOverride prfOld prf | (OverPortO prfB v) | ItIsVect
      = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                           (TyVect (minus s' m a prfB) datatype))
               dir

  slice {ty = ty} (MkPort (TyOverride t) dir) (MkPort (TyOverride tV) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride prfOld prf | (OverPortAO prfB v) with (v)
    slice {ty = ty} (MkPort (TyOverride (TyVect s' datatype)) dir) (MkPort (TyOverride (TyVect s' datatypev)) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride prfOld prf | (OverPortAO prfB v) | ItIsVect
      = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                           (TyVect (minus s' m b prfB) datatype))
               dir

  slice {ty = ty} (MkPort (TyVect s t) dir) (MkPort (TyVect s tyV) dir) (NatOverride b) NatOverride (MkNat o) MkNat prfOld prf | (OverA x)
    = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                         (TyVect (minus s o b x) t))
             dir

  slice {ty = ty} (MkPort (TyVect s t) dir) (MkPort (TyVect s tyV) dir) (MkNat a) MkNat (NatOverride m) NatOverride prfOld prf | (OverO x)
    = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                         (TyVect (minus s m a x) t))
             dir

  slice {ty = ty} (MkPort (TyVect s t) dir) (MkPort (TyVect s tyV) dir) (NatOverride b) NatOverride (NatOverride m) NatOverride prfOld prf | (OverAO x)
    = MkPort (TyOverride {typeOuter = VectorTyDesc (minus s o a prfOld) ty}
                         (TyVect (minus s m b x) t))
             dir

--slice {ty} pTm pVal aTm aVal oTm oVal prfOld prf with (prf)
--  slice {ty} (MkPort (TyVect s t) dir) (MkPort (TyVect s tV) dir) (MkNat a) MkNat (MkNat o) MkNat prfOld prf | (NoChange x)
--

-- [ EOF ]
