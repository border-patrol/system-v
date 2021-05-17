module SystemV.Annotated.Types.Intention

import Decidable.Equality

import Toolkit.Decidable.Informative

%default total

public export
data Intention : Type where
   Data      : Intention
   Address   : Intention
   Clock     : Intention
   Reset     : Intention
   Info      : Intention
   Interrupt : Intention
   Control   : Intention
   General   : Intention

dataNotAddress : (Data = Address) -> Void
dataNotAddress Refl impossible

dataNotClock : (Data = Clock) -> Void
dataNotClock Refl impossible

dataNotReset : (Data = Reset) -> Void
dataNotReset Refl impossible

dataNotInfo : (Data = Info) -> Void
dataNotInfo Refl impossible

dataNotInterrupt : (Data = Interrupt) -> Void
dataNotInterrupt Refl impossible

dataNotControl : (Data = Control) -> Void
dataNotControl Refl impossible

dataNotGeneral : (Data = General) -> Void
dataNotGeneral Refl impossible

addressNotClock : (Address = Clock) -> Void
addressNotClock Refl impossible

addressNotReset : (Address = Reset) -> Void
addressNotReset Refl impossible

addressNotInfo : (Address = Info) -> Void
addressNotInfo Refl impossible

addressNotInterrupt : (Address = Interrupt) -> Void
addressNotInterrupt Refl impossible

addressNotControl : (Address = Control) -> Void
addressNotControl Refl impossible

addressNotGeneral : (Address = General) -> Void
addressNotGeneral Refl impossible

clockNotReset : (Clock = Reset) -> Void
clockNotReset Refl impossible

clockNotInfo : (Clock = Info) -> Void
clockNotInfo Refl impossible

clockNotInterrupt : (Clock = Interrupt) -> Void
clockNotInterrupt Refl impossible

clockNotControl : (Clock = Control) -> Void
clockNotControl Refl impossible

clockNotGeneral : (Clock = General) -> Void
clockNotGeneral Refl impossible

resetNotInfo : (Reset = Info) -> Void
resetNotInfo Refl impossible

resetNotInterrupt : (Reset = Interrupt) -> Void
resetNotInterrupt Refl impossible

resetNotControl : (Reset = Control) -> Void
resetNotControl Refl impossible

resetNotGeneral : (Reset = General) -> Void
resetNotGeneral Refl impossible

infoNotInterrupt : (Info = Interrupt) -> Void
infoNotInterrupt Refl impossible

infoNotControl : (Info = Control) -> Void
infoNotControl Refl impossible

infoNotGeneral : (Info = General) -> Void
infoNotGeneral Refl impossible

interruptNotControl : (Interrupt = Control) -> Void
interruptNotControl Refl impossible

interruptNotGeneral : (Interrupt = General) -> Void
interruptNotGeneral Refl impossible

controlNotGeneral : (Control = General) -> Void
controlNotGeneral Refl impossible

export
DecEq Intention where
  decEq Data Data = Yes Refl
  decEq Data Address = No dataNotAddress
  decEq Data Clock = No dataNotClock
  decEq Data Reset = No dataNotReset
  decEq Data Info = No dataNotInfo
  decEq Data Interrupt = No dataNotInterrupt
  decEq Data Control = No dataNotControl
  decEq Data General = No dataNotGeneral

  decEq Address Data = No (negEqSym dataNotAddress)
  decEq Address Address = Yes Refl
  decEq Address Clock = (No addressNotClock)
  decEq Address Reset = (No addressNotReset)
  decEq Address Info = (No addressNotInfo)
  decEq Address Interrupt = (No addressNotInterrupt)
  decEq Address Control = (No addressNotControl)
  decEq Address General = (No addressNotGeneral)

  decEq Clock Data = No (negEqSym dataNotClock)
  decEq Clock Address = No (negEqSym addressNotClock)
  decEq Clock Clock = Yes Refl
  decEq Clock Reset = No clockNotReset
  decEq Clock Info = No clockNotInfo
  decEq Clock Interrupt = No clockNotInterrupt
  decEq Clock Control = No clockNotControl
  decEq Clock General = No clockNotGeneral

  decEq Reset Data = No (negEqSym dataNotReset)
  decEq Reset Address = No (negEqSym addressNotReset)
  decEq Reset Clock = No (negEqSym clockNotReset)
  decEq Reset Reset = Yes Refl
  decEq Reset Info = No resetNotInfo
  decEq Reset Interrupt = No resetNotInterrupt
  decEq Reset Control = No resetNotControl
  decEq Reset General = No resetNotGeneral

  decEq Info Data = No (negEqSym dataNotInfo)
  decEq Info Address = No (negEqSym addressNotInfo)
  decEq Info Clock = No (negEqSym clockNotInfo)
  decEq Info Reset = No (negEqSym resetNotInfo)
  decEq Info Info = Yes Refl
  decEq Info Interrupt = No infoNotInterrupt
  decEq Info Control = No infoNotControl
  decEq Info General = No infoNotGeneral

  decEq Interrupt Data = No (negEqSym dataNotInterrupt)
  decEq Interrupt Address = No (negEqSym addressNotInterrupt)
  decEq Interrupt Clock = No (negEqSym clockNotInterrupt)
  decEq Interrupt Reset = No (negEqSym resetNotInterrupt)
  decEq Interrupt Info = No (negEqSym infoNotInterrupt)
  decEq Interrupt Interrupt = Yes Refl
  decEq Interrupt Control = No interruptNotControl
  decEq Interrupt General = No interruptNotGeneral

  decEq Control Data = No (negEqSym dataNotControl)
  decEq Control Address = No (negEqSym addressNotControl)
  decEq Control Clock = No (negEqSym clockNotControl)
  decEq Control Reset = No (negEqSym resetNotControl)
  decEq Control Info = No (negEqSym infoNotControl)
  decEq Control Interrupt = No (negEqSym interruptNotControl)
  decEq Control Control = Yes Refl
  decEq Control General = No controlNotGeneral

  decEq General Data = No (negEqSym dataNotGeneral)
  decEq General Address = No (negEqSym addressNotGeneral)
  decEq General Clock = No (negEqSym clockNotGeneral)
  decEq General Reset = No (negEqSym resetNotGeneral)
  decEq General Info = No (negEqSym infoNotGeneral)
  decEq General Interrupt = No (negEqSym interruptNotGeneral)
  decEq General Control = No (negEqSym controlNotGeneral)
  decEq General General = Yes Refl

public export
data Compatible : (l,r : Intention) -> Type
  where
    SameIntention : Compatible w       w
    GAny     : Compatible General a
    AnyG     : Compatible a       General


negCompatibleSym : (Compatible l r -> Void) -> Compatible r l -> Void
negCompatibleSym f SameIntention = f SameIntention
negCompatibleSym f GAny = f AnyG
negCompatibleSym f AnyG = f GAny


daNotCompat : Compatible Data Address -> Void
daNotCompat SameIntention impossible

dcNotCompat : Compatible Data Clock -> Void
dcNotCompat SameIntention impossible

drNotCompat : Compatible Data Reset -> Void
drNotCompat SameIntention impossible

ddNotCompat : Compatible Data Info -> Void
ddNotCompat SameIntention impossible

diNotCompat : Compatible Data Interrupt -> Void
diNotCompat SameIntention impossible

dctrlNotCompat : Compatible Data Control -> Void
dctrlNotCompat SameIntention impossible

acNotCompat : Compatible Address Clock -> Void
acNotCompat SameIntention impossible

arNotCompat : Compatible Address Reset -> Void
arNotCompat SameIntention impossible

aiNotCompat : Compatible Address Info -> Void
aiNotCompat SameIntention impossible

aitNotCompat : Compatible Address Interrupt -> Void
aitNotCompat SameIntention impossible

actrlNotCompat : Compatible Address Control -> Void
actrlNotCompat SameIntention impossible

crNotCompat : Compatible Clock Reset -> Void
crNotCompat SameIntention impossible

ciNotCompat : Compatible Clock Info -> Void
ciNotCompat SameIntention impossible

cintNotCompat : Compatible Clock Interrupt -> Void
cintNotCompat SameIntention impossible

ccNotCompatc : Compatible Clock Control -> Void
ccNotCompatc SameIntention impossible

riNotCompat : Compatible Reset Info -> Void
riNotCompat SameIntention impossible

rintNotCompat : Compatible Reset Interrupt -> Void
rintNotCompat SameIntention impossible

rcNotCompat : Compatible Reset Control -> Void
rcNotCompat SameIntention impossible

infoINotCompat : Compatible Info Interrupt -> Void
infoINotCompat SameIntention impossible

infoCNotCompat : Compatible Info Control -> Void
infoCNotCompat SameIntention impossible


interCNotCompat : Compatible Interrupt Control -> Void
interCNotCompat SameIntention impossible

public export
data Error = TypesDiffer

export
compatible : (l,r : Intention) -> DecInfo Intention.Error (Compatible l r)
compatible Data Data = Yes SameIntention
compatible Data Address = No TypesDiffer daNotCompat
compatible Data Clock = No TypesDiffer dcNotCompat
compatible Data Reset = No TypesDiffer drNotCompat
compatible Data Info = No TypesDiffer ddNotCompat
compatible Data Interrupt = No TypesDiffer diNotCompat
compatible Data Control = No TypesDiffer dctrlNotCompat
compatible Data General = Yes AnyG

compatible Address Data = No TypesDiffer $ negCompatibleSym daNotCompat
compatible Address Address = Yes SameIntention
compatible Address Clock = No TypesDiffer acNotCompat
compatible Address Reset = No TypesDiffer arNotCompat
compatible Address Info = No TypesDiffer aiNotCompat
compatible Address Interrupt = No TypesDiffer aitNotCompat
compatible Address Control = No TypesDiffer actrlNotCompat
compatible Address General = Yes AnyG

compatible Clock Data = No TypesDiffer (negCompatibleSym dcNotCompat)
compatible Clock Address = No TypesDiffer (negCompatibleSym acNotCompat)
compatible Clock Clock = Yes SameIntention
compatible Clock Reset = No TypesDiffer crNotCompat
compatible Clock Info = No TypesDiffer ciNotCompat
compatible Clock Interrupt = No TypesDiffer cintNotCompat
compatible Clock Control = No TypesDiffer ccNotCompatc
compatible Clock General = Yes AnyG

compatible Reset Data = No TypesDiffer (negCompatibleSym drNotCompat)
compatible Reset Address = No TypesDiffer (negCompatibleSym arNotCompat)
compatible Reset Clock = No TypesDiffer (negCompatibleSym crNotCompat)
compatible Reset Reset = Yes SameIntention
compatible Reset Info = No TypesDiffer riNotCompat
compatible Reset Interrupt = No TypesDiffer rintNotCompat
compatible Reset Control = No TypesDiffer rcNotCompat
compatible Reset General = Yes AnyG

compatible Info Data = No TypesDiffer (negCompatibleSym ddNotCompat)
compatible Info Address = No TypesDiffer (negCompatibleSym aiNotCompat)
compatible Info Clock = No TypesDiffer (negCompatibleSym ciNotCompat)
compatible Info Reset = No TypesDiffer (negCompatibleSym riNotCompat)
compatible Info Info = Yes SameIntention
compatible Info Interrupt = No TypesDiffer infoINotCompat
compatible Info Control = No TypesDiffer infoCNotCompat
compatible Info General = Yes AnyG

compatible Interrupt Data = No TypesDiffer (negCompatibleSym diNotCompat)
compatible Interrupt Address = No TypesDiffer (negCompatibleSym aitNotCompat)
compatible Interrupt Clock = No TypesDiffer (negCompatibleSym cintNotCompat)
compatible Interrupt Reset = No TypesDiffer (negCompatibleSym rintNotCompat)
compatible Interrupt Info = No TypesDiffer (negCompatibleSym infoINotCompat)
compatible Interrupt Interrupt = Yes SameIntention
compatible Interrupt Control = No TypesDiffer interCNotCompat
compatible Interrupt General = Yes AnyG

compatible Control Data = No TypesDiffer (negCompatibleSym dctrlNotCompat)
compatible Control Address = No TypesDiffer (negCompatibleSym actrlNotCompat)
compatible Control Clock = No TypesDiffer (negCompatibleSym ccNotCompatc)
compatible Control Reset = No TypesDiffer (negCompatibleSym rcNotCompat)
compatible Control Info = No TypesDiffer (negCompatibleSym infoCNotCompat)
compatible Control Interrupt = No TypesDiffer (negCompatibleSym interCNotCompat)
compatible Control Control = Yes SameIntention
compatible Control General = Yes AnyG
compatible General r = Yes GAny


-- [ EOF ]
