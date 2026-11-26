import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_19299 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16238126 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [5, 9]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.and, [0, 5]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [10, 14]⟩,
      ⟨GateOp.not, [15]⟩,
      ⟨GateOp.or, [12, 16]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
