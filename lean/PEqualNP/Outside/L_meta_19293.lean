import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_19293 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16227576 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.and, [0, 10]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.and, [8, 12]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [0, 14]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.or, [11, 16]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
