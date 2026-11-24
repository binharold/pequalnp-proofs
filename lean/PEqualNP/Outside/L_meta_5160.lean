import Mathlib.Data.Finset.Card
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_5160
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma foldl_stepWire_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWire acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega
lemma foldl_stepWire_getD_lt (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl stepWire acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : w < (stepWire acc g).length := by
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
