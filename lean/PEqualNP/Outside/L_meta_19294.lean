import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_19294 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16235582 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨GateOp.and, [0, 5]⟩,
      ⟨GateOp.or, [1, 9]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [11, 13]⟩,
      ⟨GateOp.or, [10, 14]⟩,
      ⟨GateOp.not, [15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
