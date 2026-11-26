import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_19296 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236078 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨GateOp.or, [5, 9]⟩,
      ⟨GateOp.and, [1, 10]⟩,
      ⟨GateOp.and, [0, 5]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [1, 13]⟩,
      ⟨GateOp.not, [14]⟩,
      ⟨GateOp.or, [11, 15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
