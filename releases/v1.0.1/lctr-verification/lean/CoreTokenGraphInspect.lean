import CoreTokenGraph
import Lean
open LCTR.CoreTokenGraph
def tokenJson (t : Token) : Lean.Json := Lean.toJson [series t, index t]
def main : IO Unit := do
  let ts : List Token := (List.finRange 6).flatMap fun s =>
    (List.finRange (count s)).map fun i => ⟨s, i⟩
  let edges := ts.flatMap fun a => ts.filterMap fun b =>
    if Edge a b then some (Lean.Json.arr #[tokenJson a, tokenJson b]) else none
  let designatedPairs := ts.flatMap fun a => ts.filterMap fun b =>
    if designated a b then some (Lean.Json.arr #[tokenJson a, tokenJson b]) else none
  let ranks := ts.map fun t => Lean.Json.arr #[tokenJson t, Lean.toJson [(rank t).1, (rank t).2]]
  IO.println (Lean.Json.mkObj [
    ("tokens", Lean.Json.arr (ts.map tokenJson).toArray),
    ("edges", Lean.Json.arr edges.toArray),
    ("designated", Lean.Json.arr designatedPairs.toArray),
    ("ranks", Lean.Json.arr ranks.toArray)]).compress
