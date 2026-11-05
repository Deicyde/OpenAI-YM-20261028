import YM.AnalyticBridge.VERIFIED_RESET_STEP.Geometry
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Placement
import YM.Push.ABSOLUTE_SUMS.Footprint
import YM.Push.LOCAL_SPLITTING.Merge
import YM.Push.PRICE_COMPILER.Canonical
import YM.Push.PRICE_COMPILER.Support

/-! Summability across (path,site,seat) and all raw residual records with
absolute addresses. The bills in `soft` already ask a stronger exponent (+1)
for the final H01 fusion. This is an output *step-local* exponent, not a
loan from the NEXT call. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG Push.AbsoluteSums Extra.Iteration Geo Residual
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint}

namespace Quotes
abbrev anchored {ι : Type*} (p : BudgetPoint) (X : ι → RegularAddress n) (k : ι → ℝ) (c : ℝ) :=
  ∀ o, SumBudget (fun i => if (X i).site=o then p.mass (X i).support (k i) else 0) c
def preExponent (p : BudgetPoint) := p.supportExponent+3
abbrev early {ι : Type*} (p : BudgetPoint) (X : ι → RegularAddress n) (k : ι → ℝ) (c : ℝ) :=
  Footprint.Anchored (fun i => (X i).site) k (fun i => coverNumber p.B (X i).support) (preExponent p) c
def resetFee (G : Gauge) (p : BudgetPoint) := Real.exp (81*p.supportExponent)*resetLoss G p
def softReset (G : Gauge) (p : BudgetPoint) (H : ℝ) :=
    Footprint.payment 1 (4*p.B+2) 0 1 (resetLoss G p) H (p.supportExponent+1) 81
lemma segment {ι : Type*} (X : ι → RegularAddress n) {k : ι → ℝ} {c : ℝ} (h : ∀ i, 0 ≤ k i) (hh : early p X k c) :
    anchored p X k c := by
  intro o; refine Cost.mono (hh o) (fun i => ?_) fun i => ?_
  · unfold BudgetPoint.mass; have h := h i; split <;> positivity
  split
  next he => rw [BudgetPoint.mass,mul_comm (k _)]; gcongr
             · exact h i
             unfold preExponent; linarith
  exact le_rfl
lemma enlarging (G : Gauge) (X : ℕ → RegularAddress n) {k : ℕ → ℝ} {c : ℝ}
    (hB : 2 ≤ p.B) (h : ∀ i, 0 ≤ k i) (hh : early p X k c) :
    anchored p (enlarges ∘ X) (fun i => resetLoss G p*k i) (resetFee G p*c) ∧ Ac.Hit (expand ∘ X) p.B (fun i => resetLoss G p*k i)
      (p.supportExponent+1) (softReset G p c) := by
  have hz := loss_pos G p
  have he := p.exponent_pos
  have ht := segment X h hh
  refine ⟨fun o => ?_,?_⟩
  · refine Cost.mono (Cost.scale (ht o) (resetFee G p) (by unfold resetFee; positivity)) ?_ ?_
    · intro i; split
      · unfold BudgetPoint.mass; have := h i; positivity
      exact le_rfl
    intro i; dsimp [enlarges,BudgetPoint.mass,resetFee]; split
    next _ =>
      have hi := enlarge p (X i) hB; rw [mul_mul_mul_comm, ← Real.exp_add]; gcongr
      · exact mul_nonneg hz.le (h i)
      exact le_trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hi : (coverNumber p.B (expand (X i)) : ℝ) ≤ coverNumber p.B (X i).support + 81) he.le) (by linarith)
    rw [mul_zero]
  exact Footprint.assigned id 1 (fun Y : Support n => by simp) _ _ h _ _ hh _ 0 _ (fun i x hx => enlarged_dist p _ x hx)
    (fun i => by rw [one_mul,add_comm]; exact_mod_cast enlarge p (X i) hB) hz.le ⟨by linarith,by norm_num,by unfold preExponent; linarith⟩
    _ (fun i => mul_nonneg hz.le (h i)) (by simp)

def anchoredFee (p : BudgetPoint) (count : ℕ) := (Fintype.card Signed : ℝ) * Real.exp (p.supportExponent*count)

lemma channel_mass {ι : Type*} (l : ι → ℕ) (X : ι → Support n) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    {σ C : ℝ} (h : SumBudget (fun i => g i * Real.exp ((σ/2)*l i)) C) (count : ℕ)
    (hM : p.supportExponent/p.B ≤ σ/2) (he : ∀ i, p.B*coverNumber p.B (X i) ≤ p.B*count + l i) :
    ∀ o : Site n, SumBudget (fun i : Seat n × ι => if i.1.2 = o then p.mass (i.1.spread (X i.2)) (g i.2) else 0) (anchoredFee p count*C) := by
  intro o
  let A := p.supportExponent
  have hC := Cost.nonneg h
  have hp : 0 < (p.B:ℝ) := Nat.cast_pos.mpr p.B_pos
  have hx (s : Seat n) : SumBudget (fun i => p.mass (s.spread (X i)) (g i)) (Real.exp (A*count) * C) := by
    refine Cost.mono (Cost.scale h _ (Real.exp_pos _).le) ?_ ?_
    · exact fun i => mul_nonneg (Real.exp_pos _).le (hg i)
    intro i; rw [BudgetPoint.mass, Seat.visit_count,mul_comm (g _), ← mul_assoc,← Real.exp_add]; gcongr
    · exact hg i
    have hl : (coverNumber p.B (X i):ℝ) ≤ count + (l i:ℝ)/p.B := by
      have hi := he i
      apply le_of_mul_le_mul_left (a:=(p.B:ℝ)) _ hp; rw [mul_add,mul_div_cancel₀ _ hp.ne']; exact_mod_cast hi
    exact (mul_le_mul_of_nonneg_left hl p.exponent_pos.le).trans (by dsimp [A]; rw [mul_add,mul_div_left_comm,mul_comm (l i:ℝ)]; gcongr)
  rw [anchoredFee,mul_assoc]; apply Cost.product (f:=fun v : Seat n => if v.2=o then Real.exp (A*count)*C else 0)
  · refine Cost.product (Cost.finite (α:=Signed) _ (by positivity)) (fun i => ⟨fun j => ?_,Summable.of_finite,?_⟩)
    · dsimp only; split <;> positivity
    rw [tsum_fintype]; simp [A]
  intro i; by_cases hi : i.2 = o
  · simpa [hi] using hx i
  simp [hi,SumBudget]

lemma channel_anchored {ι : Type*} (l : ι → ℕ) (g : ι → ℝ) (_hg : ∀ i, 0 ≤ g i) {σ C : ℝ}
    (h : SumBudget (fun i => g i * Real.exp (σ*l i)) C) :
    Footprint.Anchored (fun i : Seat n × ι => i.1.2) (fun i => g i.2) (fun i => l i.2) σ ((Fintype.card Signed : ℝ)*C) := by
  intro o
  have hC := budget_nonneg h
  refine Cost.product (f:=fun v : Seat n => if v.2=o then C else 0) ?_ ?_
  · refine Cost.product (Cost.finite _ hC) (fun i => ⟨fun j => by dsimp only; split <;> positivity,Summable.of_finite,?_⟩)
    rw [tsum_fintype]; simp
  intro i; by_cases hi : i.2 = o
  · simpa [hi]
  simp [hi,SumBudget]
lemma anchored_scale {ι : Type*} {X : ι → RegularAddress n} {k : ι → ℝ} {c r : ℝ} (hr : 0 ≤ r) (h : anchored p X k c) :
    anchored p X (fun i => r*k i) (r*c) := fun o => by simpa [BudgetPoint.mass,mul_ite,mul_left_comm r] using Cost.scale (h o) _ hr
lemma hit_scale {ι : Type*} {X : ι → Support n} {k : ι → ℝ} {c r : ℝ} {B : ℕ} {a : ℝ} (hr : 0 ≤ r) (h : Ac.Hit X B k a c) :
    Ac.Hit X B (fun i => r*k i) a (r*c) := fun o => by simpa [mul_ite,← mul_assoc] using Cost.scale (h o) _ hr

variable (G)
def lowEntry (R : PathData G) (p : BudgetPoint) (i : Seat n × Low) := i.1.reg (i.2.home R p 0) (i.2.small_home ..)
def highEntry (R : PathData G) (i : Seat n × High) := i.1.reg (i.2.home R 0) (High.small_home ..)
def lowBase (c : Clip) (p : BudgetPoint) (σ C : ℝ) := anchoredFee p lowCount * (lowFee G p σ * lowerSize c C)
def highBase (p : BudgetPoint) (σ C : ℝ) := anchoredFee p highCount * (both G p σ * (C+C))
def lowHard (p : BudgetPoint) (c : Clip) (σ C : ℝ) :=
  Footprint.payment 1 p.B 0 (σ/4) 1 (Fintype.card Signed * lowerSize c C) (p.supportExponent+1) lowCount
lemma rows (R : PathData G) (c : Clip) (p : BudgetPoint) {σ C Λ : ℝ} (h : R.Bounds c σ C Λ) (hw : Width p c σ) :
    anchored p (n:=n) (lowEntry G R p) (fun i => |i.2.mark R c| * lowCost G p (i.2.length R)) (lowBase G c p σ C) ∧
      anchored p (n:=n) (highEntry G R) (fun i => i.2.price R p) (highBase G p σ C) ∧
      Ac.Hit (fun i : Seat n × Low => i.1.spread (i.2.home R p 0)) p.B (fun i => Real.exp ((i.2.length R:ℝ)/c.relaxation)* |i.2.mark R c|)
        (p.supportExponent+1) (lowHard p c σ C) := by
  let x := p.supportExponent
  have hB : 0 < (p.B:ℝ) := Nat.cast_pos.mpr p.B_pos
  have he := p.exponent_pos
  have hs := h.width
  have ht := hw.2.2
  have hM : x/p.B ≤ σ/2 := (div_le_div_of_nonneg_right (by dsimp [x]; linarith) hB.le).trans (ht.trans (by linarith))
  refine ⟨channel_mass (Low.length R) (fun i => i.home R p (0:Site n)) _ (fun i => mul_nonneg (abs_nonneg _) (low_nonneg ..)) (low_budget G p R h) lowCount hM (fun i => low_geometry p R i _),
    channel_mass (High.length R) (fun i => i.home R (0:Site n)) (fun i => i.price R p) (fun i => High.price_nn ..) (high_budget G p R h) highCount hM (fun i => high_geometry p R i _),?_⟩
  let g (i : Low) := Real.exp ((i.length R:ℝ)/c.relaxation)* |i.mark R c|
  have hg i : 0 ≤ g i := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hK := channel_anchored (n:=n) _ g hg (kept_debit G p R hw h)
  unfold lowHard
  refine Footprint.assigned (id : Site n → Site n) 1 (fun Y : Support n => by simp) (fun i : Seat n × Low => i.1.2) (fun i => g i.2) (fun i => hg i.2) (fun i => i.2.length R) (fun i : Seat n × Low => i.1.spread (Low.home R i.2 p (0:Site n))) hK p.B 0 p.B (C:=1) (v:=lowCount) (a:=p.supportExponent+1) (ε:=σ/4) (v':=(p.B:ℝ)⁻¹) ?_ ?_
    zero_le_one (show Footprint.reserve (3*σ/4) (p.supportExponent+1) (p.B:ℝ)⁻¹ (σ/4) from ⟨by linarith,by linarith,by rw [← div_eq_mul_inv]; linarith⟩) (fun i => g i.2) (fun i => hg i.2) (fun _ => by simp)
  · rintro i y hy; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
    simpa only [affine, separation_translate, Signed.act_zero,zero_add,id_eq] using! (spin_separation i.1.1 i.1.2 j (0:Site n)).trans_le (low_dist p R _ hj)
  intro i; rw [Seat.visit_count]
  apply le_of_mul_le_mul_left (a:=(p.B:ℝ)) ?_ hB; rw [mul_add,← mul_assoc,mul_inv_cancel₀ hB.ne',one_mul]; exact_mod_cast low_geometry p R i.2 (0:Site n)
end Quotes
end YM.AnalyticBridge.VerifiedReset
