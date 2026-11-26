import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23631

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool :=
  fun (u : Fin 4) (v : Fin 6) => (274876 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 5] }
      , { op := GateOp.or, inputs := [2, 6] }
      , { op := GateOp.or, inputs := [7, 8] }
      , { op := GateOp.or, inputs := [12, 9] }
      , { op := GateOp.or, inputs := [1, 4] }
      , { op := GateOp.or, inputs := [1, 13] }
      , { op := GateOp.or, inputs := [11, 15] }
      , { op := GateOp.and, inputs := [10, 16] }
      , { op := GateOp.or, inputs := [11, 3] }
      , { op := GateOp.and, inputs := [14, 18] }
      , { op := GateOp.or, inputs := [19, 17] }
      ]
    output := 20 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide

end PEqualNP.Outside.L_meta_23631

theorem PEqualNP.Outside.L_meta_23631 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274876 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_23631.upperC, PEqualNP.Outside.L_meta_23631.upper_mono, by decide, PEqualNP.Outside.L_meta_23631.upper_rep⟩
