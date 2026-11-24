import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm in
theorem PEqualNP.Outside.R_meta_1764_101
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (normalForm : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1) (x5 : x2.Walk x4 x4), x5.IsCycle → (5 : ℕ) ≤ x5.length) → x2.edgeFinset.Nonempty → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → (PEqualNP.MetaComplexity.circuitFun x1 x6 = fun (x8 : Fin x1 → Bool) => Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x9 ∧ PEqualNP.TopForm.TopForm x2 x9 ∧ x9.size ≤ x6.size ∧ (x2.edgeFinset \ PEqualNP.TopForm.Ustar x2 x9).card ≤ x9.size + (1 : ℕ))
    (eliminate : ∃ a b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      G.edgeFinset.Nonempty → ∀ C : Circuit, IsLeastAO G C →
      ∃ v ∈ G.support, ∃ D : Circuit, Monotone2 D ∧
        circuitFun n D = NestedCover.graphFun (G.deleteIncidenceSet v) ∅ ∧
        G.degree v + b * D.size ≤ a + b * C.size) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x2 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ → {x10 ∈ x3.edgeFinset | ¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ (x13 : Fin x7.gates.length), PEqualNP.EdgeOwnership.Owns x2 x7 (↑x13) x11 x12 ∧ ∀ (x14 x15 : Fin x2), PEqualNP.EdgeOwnership.gateVal x2 x7 (↑x13) (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true → x3.Adj x14 x15}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  have normalize (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (girth : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length)
      (edges : G.edgeFinset.Nonempty) (C : Circuit) (mono : Monotone2 C)
      (computes : circuitFun n C = NestedCover.graphFun G ∅) :
      ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size := by
    obtain ⟨D, least, _, bound, _⟩ := normalForm n G girth edges C mono
      (by rw [computes]; funext x; simp [NestedCover.graphFun])
    exact ⟨D, least, bound⟩
  obtain ⟨a, b, step⟩ := eliminate
  refine ⟨a + b, ?_⟩
  intro n G inst _ girth C mono computes
  apply (Finset.card_filter_le _ _).trans
  by_cases edges : G.edgeFinset.Nonempty
  swap
  · simp [Finset.not_nonempty_iff_eq_empty.mp edges]
  obtain ⟨least, hLeast, hSize⟩ := normalize n G girth edges C mono computes
  have telescope (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      (∀ (v : Fin n) (w : F.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ Q : Circuit, IsLeastAO F Q →
        F.edgeFinset.card ≤ a * p + b * Q.size := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F dec hp hg Q hQ
      by_cases hE : F.edgeFinset.Nonempty
      swap
      · simp [Finset.not_nonempty_iff_eq_empty.mp hE]
      obtain ⟨v, hv, D, hD, computesD, price⟩ := step n F hg hE Q hQ
      let R := F.deleteIncidenceSet v
      have hpos : 0 < F.support.ncard := by
        rw [← Set.fintypeCard_eq_ncard]
        exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
      have hdrop : R.support.ncard ≤ F.support.ncard - 1 := by
        simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
      have hlt : R.support.ncard < p := by omega
      have hcy (u : Fin n) (w : R.Walk u u) (cy : w.IsCycle) : 5 ≤ w.length := by
        let h := F.deleteIncidenceSet_le v
        simpa only [SimpleGraph.Walk.length_mapLe] using hg u (w.mapLe h) (cy.mapLe h)
      have residual : R.edgeFinset.card ≤ a * R.support.ncard + b * D.size := by
        by_cases remaining : R.edgeFinset.Nonempty
        · obtain ⟨D', hD', cost⟩ := normalize n R hcy remaining D hD computesD
          exact (smaller R.support.ncard hlt R rfl hcy D' hD').trans
            (Nat.add_le_add_left (Nat.mul_le_mul_left b cost) _)
        · simp [Finset.not_nonempty_iff_eq_empty.mp remaining]
      have removed : R.edgeFinset.card = F.edgeFinset.card - F.degree v :=
        F.card_edgeFinset_deleteIncidenceSet v
      have hd : F.degree v ≤ F.edgeFinset.card :=
        F.degree_le_card_edgeFinset v
      have budget := Nat.mul_le_mul_left a (show R.support.ncard + 1 ≤ p by omega)
      rw [Nat.mul_add, Nat.mul_one] at budget
      omega
  have bound := telescope G.support.ncard G rfl girth least hLeast
  have vertices := (support n G least hLeast).trans (Nat.add_le_add_right hSize 1)
  have gates := Nat.mul_le_mul_left b (hSize.trans (Nat.le_succ C.size))
  rw [Nat.add_mul]
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left a vertices) gates)
