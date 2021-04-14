||| A collection of utlities to make life easier.
|||
||| This consists of:
|||
|||  + some syntactic sugar to make functions detailing renaming,
|||    weakening, and substitution more like those seen in PLFA.
|||
|||  + Some data structures to make working with collections of
|||    dependent types easier.
module SystemV.Common.Utilities

import public Data.List.Elem
import public Data.Vect
import public Data.Vect.Elem
import public Data.Fin
import public Data.DPair

import public Toolkit.Data.List.DeBruijn

import public Toolkit.Data.DList
import public Toolkit.Data.DList.Elem
import public Toolkit.Data.DList.DeBruijn

%default total

namespace Vect

  ||| Append `x` to the head of `xs`.
  public export
  (+=) : (xs : Vect n a) -> (x : a) -> Vect (S n) a
  (+=) xs x = x :: xs


-- --------------------------------------------------------------------- [ EOF ]
