import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_19251 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577382 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [4, 10]⟩,
      ⟨GateOp.and, [5, 11]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [1, 13]⟩,
      ⟨GateOp.and, [1, 13]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.and, [14, 16]⟩,
      ⟨GateOp.or, [12, 17]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
