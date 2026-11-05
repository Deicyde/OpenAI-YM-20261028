import YM.Next.EXTRACTION.Relay
import YM.Next.FLUCTUATIONS.Kernel
import YM.Next.PHASE.Assembly
import YM.Push.PRICE_COMPILER.Basic

/-!
# The price currency for actual path data

1179, 2961 `CRn`. A formal handoff that counts the actual
path lengths, retaining arbitrarily many terms and using `SumBudget` (not
spending a comparison of two `tsum`s without their certificates).
Give also a uniform cost lemma at any narrower width with any finite
polynomial weight. Prices are coefficients norms in the *B70* color
conventions (`Atom.magnitude`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Precision Exterior
open scoped Topology Matrix.Norms.Frobenius BigOperators

/-- Currency cost from exponent surplus `τ>0`. Example estimate; works
for all lengths, doesn't care about the period. -/
def momentFactor (d : ℕ) (τ : ℝ) : ℝ := (1 + (d+1 : ℝ) / τ) ^ d

lemma momentFactor_one (d : ℕ) {τ : ℝ} (h : 0 < τ) : 1 ≤ momentFactor d τ :=
    one_le_pow₀ (le_add_of_nonneg_right (by positivity))



lemma pays_moment (d n : ℕ) {τ : ℝ} (h : 0 < τ) :
    (1 + (n:ℝ)) ^ d ≤ momentFactor d τ * Real.exp (τ*n) := by
  let r : ℝ := τ / (d + 1 : ℝ)
  have hr : 0 < r := by unfold r; positivity
  have hn : 0 ≤ r*n := by positivity
  let K := 1 + r⁻¹
  have he : (1 + (n:ℝ)) ≤ K * Real.exp (r*n) := calc
    _ ≤ K * (r*n+1) := by
      have hh : 0 ≤ r⁻¹ := by positivity
      have hg : r⁻¹*(r*n)=n := by field_simp
      unfold K; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by unfold K; positivity)
  have hf : (d:ℝ) * r ≤ τ := by
    unfold r; have hh : 0 < (d:ℝ)+1 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hh]; linarith
  have ha : (d:ℝ) * (r*n) ≤ τ*n := by rw [← mul_assoc]; gcongr
  have hK : K = 1 + (d+1:ℝ) / τ := by unfold K r; rw [inv_div]
  calc
    _ ≤ (K * Real.exp (r*n)) ^ d := pow_le_pow_left₀ (by positivity) he d
    _ = K ^ d * Real.exp ((d:ℝ) * (r*n)) := by rw [mul_pow, Real.exp_nat_mul]
    _ ≤ _ := by
      rw [hK, momentFactor]
      gcongr

lemma buys_exponential (d n : ℕ) {σ t : ℝ} (h : σ < t) :
    Real.exp (σ*n) * (1+(n:ℝ)) ^ d ≤ momentFactor d (t-σ) * Real.exp (t*n) := calc
  _ ≤ Real.exp (σ*n) * (momentFactor d (t-σ) * Real.exp ((t-σ)*n)) :=
    mul_le_mul_of_nonneg_left (pays_moment d n (sub_pos.mpr h)) (by positivity)
  _ = _ := by rw [mul_left_comm, ← Real.exp_add]; ring_nf

section Path
variable {G : Gauge}

/-- Symbolic amount estimates can be kept separate per kind of term. -/
structure PathMass (W : PathData G) (σ rows two three four : ℝ) : Prop where
  pos : 0 < σ
  row (p : PlaqAxes) : SumBudget (fun i => |(W.row p i).1| * Real.exp (σ * (W.row p i).2.length)) rows
  loop : SumBudget (fun i => (W.loop i).budget σ) two
  cubic : SumBudget (fun i => (W.cubic i).budget σ) three
  quartic : SumBudget (fun i => (W.quartic i).budget σ) four

/-- Non-numerical normalizations with THESE paths, still input. The
infinite sums here acquire their Summable receipts via `PathMass` below. -/
structure Normalized (W : PathData G) (c : Clip) : Prop where
  invariant i : (W.loop i).Invariant ∧ (W.cubic i).Invariant ∧ (W.quartic i).Invariant
  metric : W.metric_zero c
  jets : W.loop_jets

lemma atom_magnitude_nonneg {d : ℕ} (p : Atom G d) : 0 ≤ p.magnitude := by unfold Atom.magnitude; positivity
lemma budget_mono {d : ℕ} (p : Atom G d) {s t : ℝ} (h : s ≤ t) : p.budget s ≤ p.budget t := by
  unfold Atom.budget; have := atom_magnitude_nonneg p; gcongr

lemma sum_atoms_mono {t v a b : ℝ} {d : ℕ} {F : ℕ → Atom G d} (hs : SumBudget (fun i => (F i).budget t) a)
    (h : v ≤ t) (he : a ≤ b) : SumBudget (fun i => (F i).budget v) b :=
  sumBudget_mono hs (fun i => mul_nonneg (atom_magnitude_nonneg _) (by positivity))
    (fun i => budget_mono (F i) h) he

lemma length_exp_mono (n : ℕ) {s t : ℝ} (h : s ≤ t) : Real.exp (s*n) ≤ Real.exp (t*n) := by gcongr

lemma PathMass.mono {W : PathData G} {p q A B C D x y z u : ℝ} (h : PathMass W p A B C D)
    (hz : 0 < q) (hq : q ≤ p) (ha : A ≤ x) (hb : B ≤ y) (hc : C ≤ z) (hd : D ≤ u) : PathMass W q x y z u :=
  ⟨hz, fun i => sumBudget_mono (h.row i) (fun _ => by positivity)
    (fun _ => mul_le_mul_of_nonneg_left (length_exp_mono _ hq) (by positivity)) ha,
    sum_atoms_mono h.loop hq hb,sum_atoms_mono h.cubic hq hc,sum_atoms_mono h.quartic hq hd⟩

/-- Polynomial moment cost interface on the slot arrays. -/
lemma moment_mass {ι : Type*} (n : ι → ℕ) {a σ t : ℝ} (s : ℕ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (h : SumBudget (fun i => p i * Real.exp (t * n i)) a) (ht : σ < t) :
    SumBudget (fun i => p i * Real.exp (σ * n i) * (1+(n i:ℝ))^s) (momentFactor s (t-σ) * a) := by
  let C := momentFactor s (t-σ)
  have he : 0 ≤ C := zero_le_one.trans (momentFactor_one s (sub_pos.mpr ht))
  let F := fun i => p i * Real.exp (t * n i)
  have hx : SumBudget (fun i => C * F i) (C*a) := ⟨fun i => mul_nonneg he (h.1 i),
    h.2.1.mul_left C, (Eq.trans_le (tsum_mul_left) (mul_le_mul_of_nonneg_left h.2.2 he))⟩
  apply sumBudget_mono hx _ _ le_rfl
  · intro i; have := hp i; positivity
  intro i; dsimp only [C, F]; rw [mul_assoc, mul_left_comm (momentFactor ..)]
  exact mul_le_mul_of_nonneg_left (buys_exponential s (n i) ht) (hp i)

lemma moment_atoms {k : ℕ} {F : ℕ → Atom G k} {σ t b : ℝ} (h : SumBudget (fun i => (F i).budget t) b)
    (ht : σ < t) (s : ℕ) : SumBudget (fun i => (F i).budget σ * (1 + ((F i).length:ℝ))^s) (momentFactor s (t-σ) * b) :=
  moment_mass _ s _ (fun _ => atom_magnitude_nonneg _) h ht

private lemma displacement (w : Walk) (x : Cover) (l : Axis) : ((stop x w l) - x l).natAbs ≤ w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons d w ih =>
    have hb : ((d.vec : Cover) l).natAbs ≤ 1 := by
      rcases d with ⟨j,z|z⟩ <;> by_cases h : l=j <;> simp [Step.vec,h]
    simp only [stop,List.length]
    let t : Cover := x+d.vec
    have he : stop (x+d.vec) w l - x l = (stop t w l - t l)+(d.vec : Cover) l := by dsimp [t]; omega
    rw [he]; exact (Int.natAbs_add_le ..).trans (Nat.add_le_add (ih t) hb)

lemma offset_le (s : Slot) (l : Axis) : (s.offset l).natAbs ≤ s.length := by
  have he := displacement s.walk 0 l
  simp only [Pi.zero_apply, sub_zero] at he
  exact he.trans (Nat.le_add_right ..)

lemma loop_offset_le (s : Atom G 2) (l : Axis) :
    (((s.leg 1).offset l) - (s.leg 0).offset l).natAbs ≤ s.length := by
  rw [sub_eq_add_neg]; refine (Int.natAbs_add_le ..).trans ?_
  rw [Int.natAbs_neg, Atom.length, Fin.sum_univ_two, add_comm ((s.leg 0).length)]
  exact Nat.add_le_add (offset_le ..) (offset_le ..)

lemma loop_coeff_le (W : PathData G) (i : Fin 2 → PlaqAxes) (x : Fin 2 → G.ColorIndex) (k : ℕ) :
    ‖W.loop_coeff i x k‖ ≤ (W.loop k).magnitude := by
  unfold PathData.loop_coeff; split
  · exact Finset.single_le_sum (fun a _ => abs_nonneg ((W.loop k).coeff a)) (Finset.mem_univ x)
  rw [norm_zero]; exact atom_magnitude_nonneg _

/-- Obtain the unweighted (period-independent!) summability receipts.
Thus one can ask for the actual amount estimates without asking also
for their summability consequences separately. -/
lemma PathMass.bounds {W : PathData G} {t v b C D : ℝ} (h : PathMass W t v b C D)
    {c : Clip} (he : Normalized W c) {u : ℝ} (hx : v ≤ u) (hc : C ≤ u) (hd : D ≤ u) :
    W.Bounds c t u b := by
  have hv := h.mono h.pos le_rfl hx le_rfl hc hd
  refine ⟨h.pos,hv.row,hv.loop,hv.cubic,hv.quartic,he.invariant, ?_, he.metric, ?_,he.jets⟩
  · intro p q
    refine Summable.of_norm ?_
    apply (h.row p).2.1.of_nonneg_of_le (fun _ => norm_nonneg _)
    intro i; split_ifs
    · apply le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp _)
      exact mul_nonneg h.pos.le (by positivity)
    rw [norm_zero]; positivity
  intro i x
  have hb (s : ℕ) : SumBudget (fun j => (W.loop j).magnitude * (1+((W.loop j).length:ℝ))^s) (momentFactor s t * b) := by
    simpa only [Atom.budget, zero_mul,sub_zero,Real.exp_zero, mul_one] using moment_atoms h.loop h.pos s
  refine ⟨Summable.of_norm ?_, fun l => Summable.of_norm ?_⟩
  · exact (hb 0).2.1.of_nonneg_of_le (fun a => norm_nonneg _) (fun a => by simpa using loop_coeff_le W i x a)
  apply (hb 1).2.1.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j; rw [norm_mul,pow_one]
  refine mul_le_mul (loop_coeff_le ..) ?_ (norm_nonneg _) (atom_magnitude_nonneg _)
  rw [← norm_natAbs, Real.norm_natCast]
  exact (Nat.cast_le.mpr (loop_offset_le (W.loop j) l)).trans (le_add_of_nonneg_left zero_le_one)


end Path
end YM.Push.PriceCompiler
