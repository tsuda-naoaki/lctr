import «Chapter02PositiveControls»

namespace LCTR.Chapter02.NegativeEraseIndex

open LCTR.Chapter02
open LCTR.Chapter02.PositiveControls

def eraseZetaFromActualClockRI (ζ : Bool) : Role × Unit :=
  let ri :=
    roleInstance TinyLC tinySpec tinyBodySource sameAssignment .clock ζ
  (ri.role, ri.component)

 
 
example :
    eraseZetaFromActualClockRI true ≠
      eraseZetaFromActualClockRI false := by
  decide

end LCTR.Chapter02.NegativeEraseIndex
