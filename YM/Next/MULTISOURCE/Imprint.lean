import YM.Next.MULTISOURCE.Accrue


/-!
# Render to the actual infinite-address spectrum

This never adds/removes indices from the vacuum. It uses predetermined
available slots, costs all the requested derivative orders, and includes the
true addresses/masks in interaction. Any history planning to use these lemmas
needs the slot reservation from the start.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Wilson Lattice Marker Function Finset Pack Overlay Mix
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {n : Side} {G : Gauge}

private lemma factors (n : ℕ) : (∑ i∈Finset.range (n+1),((i.factorial:ℝ)⁻¹)) ≤ 3 := by
  have he (k : ℕ) : ((k+1).factorial:ℝ)⁻¹ ≤ (1/2:ℝ)^k := by
    have hh := Nat.factorial_mul_pow_le_factorial (m:=1) (n:=k)
    have hu : (2:ℕ)^k ≤ (k+1).factorial := by simpa only [Nat.factorial_one,one_mul,← Nat.add_comm k,
        show (1:ℕ)+1=2 from rfl] using hh
    have hg : (2:ℝ)^k ≤ (k+1).factorial := by exact_mod_cast hu
    rw [one_div, inv_pow]; exact inv_anti₀ (by positivity) hg
  rw [Finset.sum_range_succ',Nat.factorial_zero,Nat.cast_one, inv_one]
  refine le_trans (add_le_add_left (Finset.sum_le_sum (fun i _ => he i)) 1) ?_
  have hh := summable_geometric_two.sum_le_tsum (range n) (by intros; positivity)
  rw [tsum_geometric_two] at hh; linarith

variable {P : Rep G n} {o : V → Site n} {k : Hot R → ℝ} {D : Hot R → Pulse G n} {w κ : ℝ}

/-- Representatives chosen once for a final Afield (same for every part). -/
structure Writers (P : Rep G n) (κ : ℝ) (D : Hot R → Pulse G n) (o : V → Site n) (k : Hot R → ℝ) where
  slot : Pack n → ℕ
  valid i : ofAddress P.activities (slot i)=i
  taps i : ∀ U, i.zone ∩ flags P.p.threshold U=i.flagsAt → (P.activities.forced (slot i)).extraTest U
  code : Hot R × ℕ ≃ ℕ
  cash : Hot R → ℂ
  singles i : 2 ≤ i.sites.card → cash i=0
  valued i : ‖cash i‖ ≤ k i
  crop : Hot R → ℕ → Config G n → ℂ
  soil : Hot R → ℕ → Support n
  fee : Hot R → ℕ → ℝ
  plots i j : i.sites.image o ⊆ soil i j ∧ P.p.Regular (soil i j) (crop i j) ∧ 0 ≤ fee i j ∧
    ∀ b∈ i.sites.image o,P.p.supBounds b (soil i j) (crop i j) (fee i j)
  finiteCost i : SumBudget (fun j => burn P.p 0 (soil i j) * fee i j) (k i)
  collects i U : (D i).1 U = cash i + ∑' j, masked P.p.threshold (soil i j) (crop i j) U
  ticket : Hot R → Pack n → ℝ
  quantity i q : Legible P.p q ((D i).2 q) ∧ ((D i).2 q ≠ 0 → i.sites.image o ⊆ q.zone) ∧
    0 ≤ ticket i q ∧ ∀ U, ‖(D i).2 q U‖ ≤ ticket i q
  total i : (∑ q, burn P.p 0 q.zone*ticket i q) ≤ κ*k i

lemma Afield.writers [Nonempty V] (h : Room P) (H : Afield P.p κ o D k w) (hv : Injective o) :
    Nonempty (Writers P κ D o k) := by
  choose i f hi hi' hF W M b hm hs ht using fun x => (H.present x).2.2.2.2.1
  choose Q hq hv' using fun x => (H.present x).2.2.2.2.2
  haveI : Nonempty (Hot R) := Nonempty.map (Hot.one R) ‹Nonempty V›
  haveI := Classical.choice (nonempty_denumerable (Hot R × ℕ))
  refine ⟨⟨_,fun i => ((h i).choose_spec).1,fun i => ((h i).choose_spec).2, Denumerable.eqv _,i,
    fun j hh => hi' j (by rwa [card_image_of_injective _ hv]),hF, M,W,b,hm,hs,fun i U => ?_, Q,hv',hq⟩⟩
  simp only [hi,ht]

namespace Writers
variable (Y : Writers P κ D o k)

def toBands : Bands R P where
  origins := o
  units i := Y.cash (Hot.one R i)
  rays j := (Y.code.symm j).1.val
  support i := Y.soil (Y.code.symm i).1 (Y.code.symm i).2
  H i := Y.crop (Y.code.symm i).1 (Y.code.symm i).2
  marks _ j := (Y.code.symm j).1.val
  entries i j :=
    if Y.slot (ofAddress P.activities i)=i ∧ (Y.code.symm j).2=0 then
      (D ((Y.code.symm j).1)).2 (ofAddress P.activities i) else 0

omit [Fintype V] in
lemma active : Y.toBands.Active := by
  have ht i j : Legible P.p (ofAddress P.activities i) (Y.toBands.entries i j) := by
    simp only [toBands]; split
    · exact (Y.quantity ..).1
    exact Legible.zero ..
  refine ⟨fun i => (Y.code.symm i).1.property, fun i j hh => (Y.plots (Y.code.symm i).1 _).1
      (Finset.mem_image_of_mem _ hh), fun i => (Y.plots ..).2.1, fun i j => (Y.code.symm j).1.property,
    ?_,fun i j => (ht i j).reads,?_,fun i j => (ht i j).borel,fun i j => (ht i j).symmetry⟩
  · intro i j h s he
    simp only [toBands] at h; split at h
    · exact (Y.quantity _ _).2.1 h (Finset.mem_image_of_mem _ he)
    exact False.elim (h rfl)
  intro i j U he; have hj := (ht i j).inventory U he; refine ⟨hj,?_⟩
  simp only [toBands] at he; split at he <;> rename_i h
  · exact h.1 ▸ Y.taps _ U hj
  exact False.elim (he rfl)

def receipt : Stubs Y.toBands where
  a i := 3 * Y.fee (Y.code.symm i).1 (Y.code.symm i).2
  k i := if Y.toBands.entries i.1 i.2 ≠ 0 then Y.ticket (Y.code.symm i.2).1 (ofAddress P.activities i.1) else 0
  nonnegative i := mul_nonneg (by norm_num) (Y.plots ..).2.2.1
  usable i := by split; exact (Y.quantity ..).2.2.1; exact le_rfl
  kernels := by
    intro i x h; let c := Y.fee (Y.code.symm i).1 (Y.code.symm i).2
    obtain ⟨ht,hC⟩ := (Y.plots (Y.code.symm i).1 (Y.code.symm i).2).2.2.2 (o x) (Finset.mem_image_of_mem _ h)
    refine ⟨fun _ => c,fun _ => ht,?_,fun k hi ha U hu => hC U hu k hi ha⟩
    change (∑ i ∈ _, c/_) ≤ 3*c
    simp_rw [div_eq_mul_inv,mul_comm c, ← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (factors _) ht
  supplies i j U := by
    split <;> rename_i h
    · change Y.toBands.entries i j ≠ 0 at h; simp only [toBands] at h ⊢; split at h
      · simp only [*]; apply (Y.quantity ..).2.2.2
      exact False.elim (h rfl)
    rw [not_not] at h; rw [h]; exact (norm_zero).le
  paid := by intro i H; split at H; assumption; exact False.elim ((lt_irrefl _) H)
end Writers
end YM.Multi
