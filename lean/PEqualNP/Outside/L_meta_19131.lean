import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19131_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega


noncomputable def depends {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ x : Fin n → Bool,
    posRead gs w x ≠ posRead gs w (Function.update x i true)

theorem mem_depends {n : ℕ} (gs : List Gate) (w : ℕ) (i : Fin n) :
    i ∈ depends gs w ↔ ∃ x : Fin n → Bool,
      posRead gs w x ≠ posRead gs w (Function.update x i true) := by
  classical
  simp [depends]

theorem depends_raw {n : ℕ} (gs : List Gate) (w : ℕ) (h : w < n + 1) :
    (depends (n:=n) gs w).card ≤ 1 := by
  classical
  cases w with
  | zero =>
    rw [show depends (n:=n) gs 0 = ∅ by ext i; simp [mem_depends, posRead]]
    simp
  | succ w =>
    have hw : w < n := by omega
    calc
      _ ≤ ({⟨w,hw⟩} : Finset (Fin n)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨x,hx⟩ := (mem_depends gs _ i).mp hi
        rw [pos_input gs w hw, pos_input gs w hw] at hx
        by_contra he
        have hin : (⟨w,hw⟩ : Fin n) ≠ i := Ne.symm (by simpa using he)
        exact hx (Function.update_of_ne hin true x).symm
      _ = 1 := Finset.card_singleton _

theorem depends_gate {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    let cs := (gs[j].inputs.map (clampWire (n+j))).toFinset
    depends (n:=n) gs (n+j+1) ⊆ cs.biUnion (depends gs) := by
  classical
  intro cs i hi
  obtain ⟨x, hx⟩ := (mem_depends gs _ i).mp hi
  by_contra hn
  apply hx
  let y := Function.update x i true
  have get (v : Fin n → Bool) :
      posRead gs (n+j+1) v = gs[j].op.eval
        (gs[j].inputs.map fun k => posRead gs (clampWire (n+j) k) v) := by
    change (wiresFrom gs (List.ofFn v)).getD (n+j) false = _
    have h := getD_wiresFrom_gate gs (List.ofFn v) j hj
    simpa only [List.length_ofFn,pos_clamp] using h
  rw [get x, get y]
  congr 1
  apply List.map_congr_left
  intro k hk
  by_contra hneq
  apply hn
  refine Finset.mem_biUnion.mpr ⟨clampWire (n+j) k, ?_, (mem_depends gs _ i).mpr ⟨x,hneq⟩⟩
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨k,hk,rfl⟩)

theorem num_depends {n : ℕ} (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (depends (n:=n) C.gates (clampWire (n+C.gates.length) C.output)).card ≤ C.size+1 := by
  classical
  let gs := C.gates
  let paid := Finset.Ico (n+1) (n+1+gs.length)
  let m := n+1+gs.length
  let r := clampWire (n+gs.length) C.output
  have hstep : ∀ w < m, 1 < (depends (n:=n) gs w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ depends (n:=n) gs w ⊆ cs.biUnion (depends (n:=n) gs) ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0) := by
    intro w hw hb
    have hlo : n+1 ≤ w := by
      by_contra! hh
      have he := depends_raw (n:=n) gs w hh
      omega
    let j := w-(n+1)
    have hj : j < gs.length := by dsimp [j,m] at *; omega
    have heq : n+j+1 = w := by dsimp [j]; omega
    let cs := (gs[j].inputs.map (clampWire (n+j))).toFinset
    refine ⟨cs, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      apply Finset.mem_range.mpr
      rw [← heq]
      exact clamp_lt (n+j+1) u (by omega)
    · simpa only [heq] using depends_gate (n:=n) gs j hj
    · have hpaid : w ∈ paid := by simp [paid, hlo, hw, m] at *
      simp only [hpaid, ite_true]
      calc
        cs.card ≤ (gs[j].inputs.map (clampWire (n+j))).length := List.toFinset_card_le _
        _ = gs[j].inputs.length := List.length_map _
        _ ≤ 2 := hfan _ (List.getElem_mem hj)
  have hr : ({r} : Finset ℕ) ⊆ Finset.range m := by
    simpa [r,m] using root_bound n gs.length C.output
  have bound := countUnion (depends (n:=n) gs) paid m hstep {r} hr
  have pc : paid.card = gs.length := by simp [paid]
  have hc := Finset.card_le_card (Finset.inter_subset_right (s₁:=Finset.range m) (s₂:=paid))
  have eq : ({r} : Finset ℕ).biUnion (depends (n:=n) gs) = depends (n:=n) gs r := by
    ext i
    simp
  rw [eq, Finset.card_singleton] at bound
  change (depends (n:=n) gs r).card ≤ gs.length+1
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def inputBits (a b : Fin 6) : Fin 12 → Bool :=
  fun i => decide (i.val = a.val ∨ i.val = 6 + b.val)

def target (a b : Fin 6) : Bool := xor (decide (a = 0)) (decide (b = 0))

theorem inputList : ∀ a b : Fin 6, List.ofFn (inputBits a b) = oneEach a b := by decide +kernel

theorem tests (i : Fin 12) :
    ∃ a b p q : Fin 6, target a b = false ∧ target p q = true ∧
      ∀ j : Fin 12, inputBits p q j = true →
        Function.update (inputBits a b) i true j = true := by
  fin_cases i
  · exact ⟨1, 1, 0, 1, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 1, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 2, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 3, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 4, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 5, 0, by decide, by decide, by decide⟩
  · exact ⟨1, 1, 1, 0, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 0, 1, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 0, 3, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 0, 4, by decide, by decide, by decide⟩
  · exact ⟨0, 0, 0, 5, by decide, by decide, by decide⟩

theorem lower (C : Circuit) (hm : Monotone2 C) (hc : Represents target C) : 11 ≤ C.size := by
  let r := clampWire (12+C.gates.length) C.output
  have atPair a b : posRead C.gates r (inputBits a b) = target a b := by
    dsimp only [r]
    rw [root_read, inputList]
    exact hc a b
  have all : (depends (n:=12) C.gates r) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨a,b,p,q,hab,hpq,hle⟩ := tests i
    have hy : posRead C.gates r (Function.update (inputBits a b) i true) = true :=
      pos_mono C.gates (fun g hg => (hm g hg).1) r _ _ hle (by rw [atPair, hpq])
    apply (mem_depends C.gates r i).mpr
    exact ⟨inputBits a b, by rw [atPair, hab, hy]; decide⟩
  have h := num_depends (n:=12) C (fun g hg => (hm g hg).2)
  change (depends (n:=12) C.gates r).card ≤ C.size+1 at h
  simp [all] at h
  omega

end PEqualNP.Outside.L_meta_19131_aux

theorem PEqualNP.Outside.L_meta_19131 : (¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => xor (decide (u = 0)) (decide (v = 0))) 10)) := by
  rintro ⟨C, hmono, hsize, hrep⟩
  have hlower := PEqualNP.Outside.L_meta_19131_aux.lower C hmono hrep
  omega
