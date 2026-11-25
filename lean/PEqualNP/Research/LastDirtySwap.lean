import PEqualNP.Defs.TopForm
import PEqualNP.Defs.MetaComplexityLgpMono

namespace PEqualNP.Research.LastDirtySwap
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

namespace Semantics
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma wire_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, val C (List.ofFn x) u = true → val C (List.ofFn y) u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hun : u < n
    · rw [val_input (n := n) (by simp) hun, val_input (n := n) (by simp) hun]
      simpa [hun] using hxy ⟨u, hun⟩
    · by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge (n := n) (by simp) hge]
        intro h; cases h
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk, val_gate (n := n) (by simp) hk]
        apply opMono_imp _ (mono_ops hM k hk)
        intro i hi
        by_cases hil : i < n + k
        · rw [if_pos hil, if_pos hil]
          exact ih i hil
        · rw [if_neg hil, if_neg hil]
          exact id

lemma circuit_monotone (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true :=
  wire_monotone n C hM x y hxy C.output

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

end Semantics
open Semantics

def patch {n : ℕ} (C : Circuit) (j : ℕ) (a b : Fin n) : Circuit :=
  ⟨C.gates.set j ⟨.and,[a.val,b.val]⟩, C.output⟩

private theorem at_patch {n} (C : Circuit) (j k : ℕ) (a b : Fin n) (hk : k<C.gates.length) :
    gateAt (patch C j a b) k = if j=k then ⟨.and,[a.val,b.val]⟩ else gateAt C k := by
  have hk' : k<(patch C j a b).gates.length := by simpa [patch] using hk
  rw [gateAt_eq hk',gateAt_eq hk]
  by_cases h : j=k
  · subst j; simp [patch]
  · simp [patch,h]

private theorem ao_patch {n} (C : Circuit) (h : IsAO2 n C) (j : ℕ) (a b : Fin n) :
    IsAO2 n (patch C j a b) := by
  let D := patch C j a b
  have len : D.gates.length=C.gates.length := List.length_set
  have atD (k : Nat) (hk : k<D.gates.length) :
      gateAt D k = if j=k then ⟨.and,[a.val,b.val]⟩ else gateAt C k :=
    at_patch C j k a b (len ▸ hk)
  have members (g : Gate) (hg : g∈D.gates) :
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 := by
    obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp hg
    have eqg : gateAt D k=g := (gateAt_eq hk).trans e
    rw [←eqg,atD k hk]
    split
    · exact ⟨Or.inl rfl,rfl⟩
    · have mem := gateAt_mem (C:=C) (len ▸ hk)
      exact ⟨h.1 _ mem,h.2.2 _ mem⟩
  refine ⟨fun g hg => (members g hg).1,?_,fun g hg => (members g hg).2⟩
  change ReadsBack n D
  intro k hk w hw
  rw [atD k hk] at hw
  split at hw
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl <;> omega
  · exact h.2.1 k (len ▸ hk) w hw

private theorem mono {n C} (h : IsAO2 n C) : Monotone2 C :=
  fun g hg => ⟨h.1 g hg,(h.2.2 g hg).le⟩

private theorem value_patch {n} (C : Circuit) (j : ℕ) (a b : Fin n) (hj : j<C.gates.length)
    (x : Fin n → Bool) : gateVal n (patch C j a b) j x = (x a && x b) := by
  have hx : (List.ofFn x).length=n := by simp
  have hj' : j<(patch C j a b).gates.length := by simpa [patch] using hj
  change val (patch C j a b) (List.ofFn x) (n+j)=_
  rw [val_gate hx hj',at_patch C j j a b hj]
  have ha : a.val<n+j := by omega
  have hb : b.val<n+j := by omega
  simp [GateOp.eval,ha,hb,val_input hx a.isLt,val_input hx b.isLt]

private theorem relation {n} (C : Circuit) (ao : IsAO2 n C) (j : ℕ) (a b : Fin n)
    (x : Fin n → Bool) (R : Bool → Bool → Prop) (refl : ∀ z,R z z) (stable : OpMono R)
    (w : ℕ) (changed : n+j≤w → R (gateVal n (patch C j a b) j x) (gateVal n C j x)) :
    R (val (patch C j a b) (List.ofFn x) w) (val C (List.ofFn x) w) := by
  let D := patch C j a b
  change R (val D (List.ofFn x) w) (val C (List.ofFn x) w)
  have len : D.gates.length=C.gates.length := List.length_set
  have hx : (List.ofFn x).length=n := by simp
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<n
    · rw [val_input hx raw,val_input hx raw]; exact refl _
    by_cases past : n+C.gates.length≤w
    · rw [val_ge hx (by omega : n+D.gates.length≤w),val_ge hx past]; exact refl _
    obtain ⟨k,rfl⟩ : ∃ k,w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    by_cases same : j=k
    · subst k; exact changed le_rfl
    rw [val_gate hx (by omega : k<D.gates.length),val_gate hx hk]
    rw [show gateAt D k=gateAt C k by simpa [D,same] using at_patch C j k a b hk]
    apply stable _ (ao.1 _ (gateAt_mem hk))
    intro i _
    by_cases prev : i<n+k
    · simp only [ite_eq_left prev]
      exact ih i prev (fun h => changed (by omega))
    · simp only [ite_eq_right prev]; exact refl _

private theorem graph_true {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : graphFun G ∅ x=true ↔ ∃ u v, G.Adj u v ∧ x u=true ∧ x v=true := by
  simp [graphFun]

private theorem choose_edge {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (nonempty : ∃ u v,G.Adj u v) (small : (gammaE G C j).card≤1) :
    ∃ a b, G.Adj a b ∧ ∀ u v, G.Adj u v → gateVal n C j (pairInput u v)=true →
      s(u,v)=s(a,b) := by
  by_cases hit : ∃ a b, G.Adj a b ∧ gateVal n C j (pairInput a b)=true
  · obtain ⟨a,b,adj,ha⟩ := hit
    refine ⟨a,b,adj,fun u v huv hv => ?_⟩
    apply Finset.card_le_one.mp small
    · exact Finset.mem_filter.mpr ⟨by simpa using huv,u,v,rfl,hv⟩
    · exact Finset.mem_filter.mpr ⟨by simpa using adj,a,b,rfl,ha⟩
  · obtain ⟨a,b,adj⟩ := nonempty
    exact ⟨a,b,adj,fun u v huv hv => (hit ⟨u,v,huv,hv⟩).elim⟩

private theorem edge_of_least_dirty {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C) (j : ℕ) (dirty : j∈junk G C) : ∃ a b,G.Adj a b := by
  by_contra! noEdge
  let zero : Circuit := ⟨[],n⟩
  have ao : IsAO2 n zero := by simp [IsAO2,AndOrOnly,ReadsBack,zero]
  have ex : circuitFun n zero=graphFun G ∅ := by
    funext x
    have off : graphFun G ∅ x=false := Bool.eq_false_of_not_eq_true fun e => by
      obtain ⟨u,v,adj,_,_⟩ := (graph_true G x).mp e
      exact noEdge u v adj
    rw [off]
    change (List.ofFn x).getD n false=false
    exact List.getD_eq_default _ _ (by simp)
  have le := least.2.2 zero ao ex
  have hj : j<C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp dirty).1
  change C.gates.length ≤ 0 at le
  omega

theorem replaceLast {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) (j : ℕ) (dirty : j∈junk G C) (last : ∀i∈junk G C, i≤j)
    (small : (gammaE G C j).card≤1) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size=C.size ∧ junk G D=(junk G C).erase j := by
  obtain ⟨a,b,edge,unique⟩ := choose_edge G C j (edge_of_least_dirty G C least j dirty) small
  let D := patch C j a b
  have len : D.gates.length=C.gates.length := List.length_set
  have size : D.size=C.size := len
  have hj : j<C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp dirty).1
  have ao : IsAO2 n D := ao_patch C least.1 j a b
  have safe (x : Fin n → Bool) (off : graphFun G ∅ x=false) : gateVal n D j x=false := by
    rw [show gateVal n D j x=(x a && x b) from value_patch C j a b hj x]
    apply Bool.eq_false_of_not_eq_true
    intro both
    obtain ⟨ha,hb⟩ : x a=true ∧ x b=true := by simpa only [Bool.and_eq_true] using both
    exact Bool.false_ne_true (off.symm.trans ((graph_true G x).mpr ⟨a,b,edge,ha,hb⟩))
  have shrink (x : Fin n → Bool) (off : graphFun G ∅ x=false) (i : ℕ) :
      val D (List.ofFn x) i=true → val C (List.ofFn x) i=true := by
    apply relation C least.1 j a b x (fun l r => l=true → r=true) (fun _ => id) opMono_imp
    intro _ ht
    exact (Bool.false_ne_true ((safe x off).symm.trans ht)).elim
  have detect (u v : Fin n) (adj : G.Adj u v) : circuitFun n D (pairInput u v)=true := by
    let x := pairInput u v
    have up : gateVal n C j x=true → gateVal n D j x=true := by
      intro high
      have key := unique u v adj high
      rw [show gateVal n D j x=(x a && x b) from value_patch C j a b hj x]
      rcases Sym2.eq_iff.mp key with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [x,pairInput]
    have cmp := relation C least.1 j a b x (fun l r => r=true → l=true)
      (fun _ => id) opMono_reverse C.output (fun _ => up)
    apply cmp
    change circuitFun n C x=true
    rw [least.2.1]
    exact (graph_true G x).mpr ⟨u,v,adj,by simp [x,pairInput],by simp [x,pairInput]⟩
  have correct : circuitFun n D=graphFun G ∅ := by
    funext x
    cases off : graphFun G ∅ x with
    | false =>
      apply Bool.eq_false_of_not_eq_true
      intro h
      have original : circuitFun n C x=true := shrink x off D.output h
      simp [least.2.1,off] at original
    | true =>
      obtain ⟨u,v,adj,hu,hv⟩ := (graph_true G x).mp off
      apply circuit_monotone n D (mono ao) (pairInput u v) x _ (detect u v adj)
      intro i hit
      rcases (show i=u ∨ i=v by simpa [pairInput] using hit) with rfl|rfl <;> assumption
  refine ⟨D,⟨ao,correct,fun E hE ef => size ▸ least.2.2 E hE ef⟩,size,?_⟩
  ext i
  constructor
  · intro mem
    obtain ⟨rng,op,_,x,on,off⟩ := Finset.mem_filter.mp mem
    have hiD : i<D.gates.length := Finset.mem_range.mp rng
    have hiC : i<C.gates.length := len ▸ hiD
    have ne : i≠j := by
      rintro rfl
      exact Bool.false_ne_true ((safe x off).symm.trans on)
    have same : gateAt D i=gateAt C i := by simpa [D,ne.symm] using at_patch C j i a b hiC
    refine Finset.mem_erase.mpr ⟨ne,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiC,?_,hiC,x,?_,off⟩⟩
    · rwa [←same]
    · exact shrink x off (n+i) on
  · intro mem
    obtain ⟨ne,old⟩ := Finset.mem_erase.mp mem
    have lt : i<j := lt_of_le_of_ne (last i old) ne
    obtain ⟨_,op,hiC,x,on,off⟩ := Finset.mem_filter.mp old
    have hiD : i<D.gates.length := len.symm ▸ hiC
    have same : gateAt D i=gateAt C i := by simpa [D,ne.symm] using at_patch C j i a b hiC
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hiD,same ▸ op,hiD,x,?_,off⟩
    have eq := relation C least.1 j a b x Eq (fun _ => rfl) opMono_eq (n+i) (by omega)
    exact eq.trans on

/-- If a least circuit cannot have exactly one dirty AND, the later of two dirty ANDs
activates on at least two distinct edge inputs. -/
theorem twoEdgesOfTwoDirty {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (noOne : ∀ D : Circuit, IsLeastAO G D → (junk G D).card≠1)
    (least : IsLeastAO G C) (two : (junk G C).card=2) (j : ℕ)
    (dirty : j∈junk G C) (last : ∀i∈junk G C, i≤j) : 2≤(gammaE G C j).card := by
  by_contra! low
  obtain ⟨D,leastD,_,eq⟩ := replaceLast G C least j dirty last (by omega)
  apply noOne D leastD
  rw [eq,Finset.card_erase_of_mem dirty,two]

end PEqualNP.Research.LastDirtySwap
