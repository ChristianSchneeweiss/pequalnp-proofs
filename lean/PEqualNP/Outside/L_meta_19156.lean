import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19156 :
  (∀ (n : ℕ) (i j : Fin n), ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide (u ≠ i) && decide (v ≠ j)) C) := by
  intro n i j
  let C : Circuit := ⟨[⟨GateOp.or, [i.val, n + j.val]⟩, ⟨GateOp.not, [n + n]⟩], n + n + 1⟩
  refine ⟨C, ?_, by change 2 ≤ 2; exact le_rfl, ?_⟩
  · intro g hg
    change g ∈ [⟨GateOp.or, [i.val, n + j.val]⟩, ⟨GateOp.not, [n + n]⟩] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp
  · intro u v
    let a := List.ofFn (fun t : Fin n => decide (t = u))
    let b := List.ofFn (fun t : Fin n => decide (t = v))
    let w := a ++ b
    have ha : a.length = n := List.length_ofFn
    have hb : b.length = n := List.length_ofFn
    have hw : w.length = n + n := by simp [w, ha, hb]
    have left : w.getD i.val false = decide (i = u) := by
      rw [show w = a ++ b from rfl, List.getD_append _ _ _ _ (by simpa only [ha] using i.isLt)]
      rw [List.getD_eq_getElem _ _ (by simpa only [ha] using i.isLt)]
      simp [a]
    have right : w.getD (n + j.val) false = decide (j = v) := by
      rw [show w = a ++ b from rfl, List.getD_append_right _ _ _ _ (by omega), ha,
        Nat.add_sub_cancel_left]
      rw [List.getD_eq_getElem _ _ (by simpa only [hb] using j.isLt)]
      simp [b]
    let t := GateOp.or.eval [w.getD i.val false, w.getD (n + j.val) false]
    have endRead (xs : List Bool) (x : Bool) (k : ℕ) (h : xs.length = k) :
        (xs ++ [x]).getD k false = x := by
      subst k
      simp
    have hw' : (w ++ [t]).length = n + n + 1 := by simp [hw]
    change ((w ++ [t]) ++ [!((w ++ [t]).getD (n + n) false)]).getD (n + n + 1) false =
      (decide (u ≠ i) && decide (v ≠ j))
    rw [endRead _ _ _ hw', endRead _ _ _ hw]
    dsimp only [t]
    rw [left, right]
    simp [GateOp.eval, eq_comm]
