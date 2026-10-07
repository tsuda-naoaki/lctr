import CoreFiniteAudit
open LCTR.CoreFiniteAudit LCTR.CoreTokenGraph LCTR.CoreAuditStateTransport

def allTokens : List Token := (List.finRange 6).flatMap (fun i =>
  (List.finRange (count i)).map (fun j => ⟨i,j⟩))

def counts (formed evaluated condition : Bool) : List Nat :=
  let table := runTable (fun _ => formed) (fun _ => evaluated) (fun _ => condition) 40
  let s := lookup table
  let values := allTokens.map (fun x => priority (lift (predecessorPass s x) (s x)))
  (List.finRange 5).map (fun i => values.count i.val)

#eval counts true true true
#eval counts false true true
#eval counts true false true
#eval counts true true false
