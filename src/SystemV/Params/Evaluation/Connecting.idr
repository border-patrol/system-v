module SystemV.Params.Evaluation.Connecting

import SystemV.Common.Utilities

import SystemV.Params.Types
import SystemV.Params.Terms

import SystemV.Params.Evaluation.Values
import SystemV.Params.Evaluation.Values.Overridden

%hide Alt.Overridden
%hide Alt.overridden

%default total

public export
data CanConnect : (ty   : TYPE (DATA TYPE))
               -> {tmL  : SystemV Nil ty}
               -> {tmR  : SystemV Nil ty}
               -> (valL : Value tmL)
               -> (valR : Value tmR)
                        -> Type
  where
    BothSame : (valL : Value tmL)
            -> (cL   : Overridden ty tmL valL -> Void)

            -> (valR : Value tmR)
            -> (cR   : Overridden ty tmR valR -> Void)
            -> CanConnect ty valL valR

    LeftOver : {tmL : SystemV Nil tyL}
            -> {valL : Value tmL}
            -> (Overridden ty (TyOverride tmL) (TyOverride valL))

            -> {tmR  : SystemV Nil ty}
            -> {valR : Value tmR}
            -> (cR   : Overridden ty tmR valR -> Void)

            -> Equals Universe TYPE tyL ty

            -> CanConnect ty (TyOverride valL)
                             valR

    RightOver : {tmL  : SystemV Nil ty}
             -> {valL : Value tmL}
             -> (cL   : Overridden ty tmL valL -> Void)

             -> {tmR : SystemV Nil tyR}
             -> {valR : Value tmR}
             -> (Overridden ty (TyOverride tmR) (TyOverride valR))


             -> Equals Universe TYPE ty tyR

             -> CanConnect ty valL
                              (TyOverride valR)

    BothOver  : {tmL : SystemV Nil tyL}
             -> {valL : Value tmL}
             -> (Overridden ty (TyOverride tmL) (TyOverride valL))

             -> {tmR : SystemV Nil tyR}
             -> {valR : Value tmR}
             -> (Overridden ty (TyOverride tmR) (TyOverride valR))


             -> Equals Universe TYPE tyL tyR

             -> CanConnect ty (TyOverride valL)
                              (TyOverride valR)

export
canConnect : {ty      : TYPE (DATA TYPE)}
          -> {tmL,tmR : SystemV Nil ty}
          -> (valL    : Value tmL)
          -> (valR    : Value tmR)
                     -> Maybe (CanConnect ty valL valR)
canConnect {ty} {tmL} {tmR} valL valR with (overridden valL)
  canConnect {ty} {tmL} {tmR} valL valR | l with (overridden valR)
    canConnect {ty = ty} {tmL = tmL} {tmR = tmR} valL valR | (Yes prf) | (Yes x) with (prf)
      canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = tmR} (TyOverride val) valR | (Yes prf) | (Yes x) | (IsOverridden type term val) with (x)
        canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = (TyOverride z)} (TyOverride val) (TyOverride w) | (Yes prf) | (Yes x) | (IsOverridden type term val) | (IsOverridden y z w) with (TYPE.Equality.decEq type y)
          canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = (TyOverride z)} (TyOverride val) (TyOverride w) | (Yes prf) | (Yes x) | (IsOverridden type term val) | (IsOverridden y z w) | (Yes prfWhy)
            = Just (BothOver prf x prfWhy)
          canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = (TyOverride z)} (TyOverride val) (TyOverride w) | (Yes prf) | (Yes x) | (IsOverridden type term val) | (IsOverridden y z w) | (No msgWhyNot prfWhyNot)
            = Nothing

    canConnect {ty = ty} {tmL = tmL} {tmR = tmR} valL valR | (Yes prf) | (No contra) with (prf)
      canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = tmR} (TyOverride val) valR | (Yes prf) | (No contra) | (IsOverridden type term val) with (TYPE.Equality.decEq type ty)
        canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = tmR} (TyOverride val) valR | (Yes prf) | (No contra) | (IsOverridden type term val) | (Yes prfWhy)
          = Just (LeftOver prf contra prfWhy)
        canConnect {ty = ty} {tmL = (TyOverride term)} {tmR = tmR} (TyOverride val) valR | (Yes prf) | (No contra) | (IsOverridden type term val) | (No msgWhyNot prfWhyNot) = Nothing


    canConnect {  ty = ty} {  tmL = tmL} {  tmR = tmR} valL valR | (No contra) | (Yes prf) with (prf)
      canConnect {ty = ty} {tmL = tmL} {tmR = (TyOverride term)} valL (TyOverride val) | (No contra) | (Yes prf) | (IsOverridden type term val) with (TYPE.Equality.decEq ty type)
        canConnect {ty = ty} {tmL = tmL} {tmR = (TyOverride term)} valL (TyOverride val) | (No contra) | (Yes prf) | (IsOverridden type term val) | (Yes prfWhy)
          = Just (RightOver contra prf prfWhy)
        canConnect {ty = ty} {tmL = tmL} {tmR = (TyOverride term)} valL (TyOverride val) | (No contra) | (Yes prf) | (IsOverridden type term val) | (No msgWhyNot prfWhyNot)
          = Nothing

    canConnect {  ty = ty} {  tmL = tmL} {  tmR = tmR} valL valR | (No contra) | (No f)
      = Just (BothSame valL contra valR f)

-- [ EOF ]
