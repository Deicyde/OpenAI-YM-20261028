import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ChipHeal
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Scales
import YM.Progress.STATIONARY_SCENES.Dispatch
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Change


/-!
# Local exact joint law of gauged active probes vs free probes

Read e inside active common coordinates. Don't claim determinant small on full
volumes (TV bound insensitive to the *outside* inverse). Use FreePrice &
Ledger to transfer to normalized push. Tail terms not in this statement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Local
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly  FreeResolvent Remote  Extra.Iteration.Scales MeasureTheory
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}
section price
variable {m n X : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] {D : Cost X}

omit [DecidableEq n] in
lemma entry {r : n→X} {M : Gaussian.Table n} {s C : ℝ} (h : D.Schur r r s C M) (hs : 0≤s) (i j) :
    |M i j| ≤ C := by simpa only [Cost.weight_zero,one_mul] using (h.rows.mono hs le_rfl).weighted i j
omit [DecidableEq m] in
lemma cheaply {r : m→X} {A B : ℝ} {M : Gaussian.Table m} (_ha : 0≤A)
    (h : ∀ i j, |M i j|≤A) (he : Fintype.card m*A ≤ B) : D.Schur r r 0 B M := by
  have H {M : Gaussian.Table m} (h : ∀ i j, |M i j|≤A) : D.Rows r r 0 B M := by
    refine ⟨fun i => ?_⟩
    simp only [Cost.weight_zero,one_mul]
    exact (Finset.sum_le_sum (f:=fun j => |M i j|) (g:=fun _ => A) (s:=univ) fun j _ => h i j).trans (by rw [sum_const,card_univ,nsmul_eq_mul]; exact he)
  exact ⟨H h,H (fun i j => h j i)⟩

omit [Fintype n] [DecidableEq n] in
lemma affordable {n : Type} {r : ℝ} {Q : Gaussian.Table n} (i : m ↪ n) [Fintype n] [DecidableEq n]
    (hr : 0<r) (hg : FreeResolvent.Gap Q r) {s t : ℝ} (_h : 0≤s) (hQ : Q.PosDef) (he : ∀ i j, |Q i j| ≤ t) (ht : 0≤t) (p : m → X)
    (hT : Fintype.card m*t≤s) (hR : Fintype.card m*r⁻¹≤s) :
    let A:= Q.submatrix i i
    A.PosDef ∧ D.Schur p p 0 s A ∧ D.Schur p p 0 s A⁻¹ := by
  intro M; have H := hQ.submatrix i.injective
  refine ⟨H,cheaply ht (fun j k=>he ..) hT,cheaply (inv_pos.mpr hr).le ?_ hR⟩
  exact (hg.submatrix i i.injective).point hr (M.mul_nonsing_inv (M.isUnit_iff_isUnit_det.mp H.isUnit))
end price

variable (m) [Fintype m]

def lives (F : Forest S.ratio) (U : Stores S) (o : Site c) (D : ℕ) (i : m ↪ In x U F (G:=G)) :=
  ∀ j, separation o (front U F (i j)) ≤ D
lemma reach {m : Type} [Fintype m] (o : Site c) {F : Forest S.ratio} {U : Stores S} {D : ℕ} (i : m ↪ In x U F (G:=G)) (h : lives m F U o D i) :
    (Fintype.card m:ℝ) ≤ slotCount G S D := by
  let Z := LocalJet.members S o D ×ˢ (Finset.univ (α:=G.ColorIndex))
  let T (q : m) : Z := ⟨originLink U F x G (i q), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h q⟩,Finset.mem_univ _⟩⟩
  have hc : Fintype.card m≤Fintype.card Z := Fintype.card_le_of_injective T (by intro a b h; exact i.injective ((originLink U F x G).injective (congr_arg Subtype.val h)))
  have hx : Fintype.card Z=(LocalJet.members S o D).card*Fintype.card G.ColorIndex := by rw [Fintype.card_coe,show Z.card=_ from Finset.card_product ..,Finset.card_univ]
  unfold slotCount; refine (Nat.cast_le.mpr hc).trans ?_; rw [hx,Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (LocalJet.saves S o D) (by positivity)

def room (x : ℝ) := x^(1/128:ℝ)
lemma roster (G : Gauge) (P : Patch) :
    let g (x : ℝ):=(Fintype.card (Site P.L):ℝ)*(LocalJet.grain (radiusB x)*Fintype.card Axis)*(Fintype.card G.ColorIndex)
    Tiny id g := by
  intro g
  let t:= (Fintype.card (Site P.L):ℝ)*(Fintype.card Axis)*(Fintype.card G.ColorIndex)
  have h := Tiny.mul (Tiny.const tendsto_id t (by unfold t; positivity))
    ((Tiny.mul (Tiny.const tendsto_id 3 (by norm_num)) (Tiny.cover_size) tendsto_id).pow tendsto_id 4) tendsto_id
  intro a ha; filter_upwards [h a ha] with x hx; let r : ℝ:=radiusB x; have hr : 0 ≤ r := Nat.cast_nonneg _
  unfold g LocalJet.grain; push_cast; change _ ∧ _ ≤ _; constructor
  · positivity
  refine le_trans ?_ hx.2
  calc
    _ = t*(r+r+1)^4 := by unfold t r; ring
    _ ≤ _ := by gcongr; change r+r+1≤3*(1+r); linarith

lemma limited (G : Gauge) (P : Patch) {t : ℝ} (ht : 0≤t) : ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=P →
    slotCount G S (radiusB x/4)*t ≤ room x := by
  have h := roster G P
  have he := Tiny.mul h (Tiny.const tendsto_id t ht) tendsto_id
  filter_upwards [he (1/128) (by norm_num)] with x he
  intro c f S hs
  apply le_trans _ he.2
  unfold slotCount LocalJet.chips LocalJet.grain
  have hS : Fintype.card (Site S.patch.L) = Fintype.card (Site P.L) := by simp [hs]
  rw [hS]; gcongr <;> exact Nat.div_le_self ..

lemma powers (t : ℝ) (ht : 0 ≤ t) :
    ∀ᶠ x : ℝ in atTop, let h := x^(-(1/8):ℝ); let K:=room x
    2 ≤ x ∧ 1 ≤ K ∧ (∀ n : ℝ, 0≤n → n≤K →
     n*(t*x^(-(1/4):ℝ)) ≤ h ∧ h*(2*K*n*(1+(1:ℝ)^2)+2*(K^2+K)*(n*K)) ≤ x^(-(1/16):ℝ)) ∧
    K*h≤1/2 ∧ ∀ β : ℝ, 0<β → β≤3*x → (coupling β)⁻¹*x^(-(7/8):ℝ)≤h := by
  filter_upwards [((Tiny.const tendsto_id t ht) (1/16) (by norm_num)), (Tiny.const tendsto_id 16 (by norm_num)) (1/128) (by norm_num),eventually_ge_atTop (2:ℝ)] with x hv he hx
  intro h K
  have h0 : 0<x := by linarith
  have h1 : 1≤x := by linarith
  have hi : 16≤K := he.2; have hp : 1≤K := by linarith
  have hr i j : x^i*x^(j:ℝ)=x^(i+j:ℝ) := (Real.rpow_add h0 ..).symm
  have hr' (a b : ℝ) (hb : a≤b) : x^a≤x^b := Real.rpow_le_rpow_of_exponent_le h1 hb
  have hQ : 0≤h := by unfold h; positivity
  refine ⟨hx,hp,fun n hn hn' => ?_,?_,?_⟩
  · constructor
    · calc
        _ ≤ K*(x^(1/16:ℝ)*x^(-(1/4):ℝ)) := by gcongr; exact hv.2
        _ ≤ _ := by unfold h K room; rw [hr,hr]; apply hr'; norm_num
    have hh : K^2≤K^4 := by nlinarith [sq_nonneg (K^2-1)]
    calc
      _ ≤ h*(16*K^4) := by gcongr; calc
                             _ ≤ 4*K*K+4*K^4 := by
                               have hN : n*K≤K*K := mul_le_mul_of_nonneg_right hn' (by linarith)
                               have ht : K^2+K ≤ 2*(K*K) := by nlinarith
                               have hs := mul_le_mul ht hN (by positivity : 0≤n*K) (by positivity : 0≤2*(K*K)); nlinarith
                             _ ≤ _ := by nlinarith
      _ ≤ h*(K*(K*(K*(K*K)))) := by apply mul_le_mul_of_nonneg_left _ hQ; calc
                                         _ ≤ K*K^4 := by gcongr
                                         _ = _ := by ring
      _ ≤ _ := by unfold h K room; rw [hr,hr,hr,hr,hr]; apply hr'; norm_num
  · apply le_of_mul_le_mul_left (a:=K) ?_ (by positivity)
    rw [← mul_assoc]; change K*K*h≤_
    have hh : K*K*h ≤ 1 := by unfold h K room; rw [hr,hr]; simpa using hr' _ 0 (by norm_num : (1/128:ℝ)+1/128+-(1/8) ≤ 0)
    linarith
  intro β hβ hz
  rw [coupling,inv_inv]; have hh : Real.sqrt β ≤ 2*x^(1/2:ℝ) := by rw [← Real.sqrt_eq_rpow]; nlinarith [Real.sq_sqrt (le_of_lt h0), Real.sq_sqrt (le_of_lt hβ),Real.sqrt_nonneg β,Real.sqrt_nonneg x]
  calc
    _ ≤ K*x^(1/2:ℝ)*x^(-(7/8):ℝ) := by gcongr; apply hh.trans; gcongr; linarith
    _ ≤ _ := by unfold K h room; rw [hr,hr]; apply hr'; norm_num
end YM.AnalyticBridge.LocalGaussianLaws.Local
