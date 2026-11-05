import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batches

/-!
# Collect and price actual principal log diagnostics

Local log difference controlled by A differences ONLY on the block
window (and dependencies of those entries). Applicable to compared
bathed A. Keep uniform in k,F and strings of path costs; for logs
and determinant series pair each local scalar, not each angular index
nor each eigenvector. Exponents signs independent here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse.Batch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A Z : Itinerary.Mat f G} {B m : ℕ} {η r Q : ℝ}
variable (D : Window (along (G:=G) S) B)

/-- At all real sectors. Pay as compulsory per **physical link**, not per block
read of each query. -/
lemma nearBase (hp : Torch η r Q) (h : Allow A (along S) m η r Q) (v : Bond f) :
    |joint A D v| ≤ (Fintype.card G.ColorIndex:ℝ)*((Q+1)*payE η r Q m) := by
  let k := retain η r Q; let E := (Q+1)*payE η r Q m
  have he (x) (hh : x∈Set.Icc (0:ℝ) 1) : Price (along S) (along S) (intensity D A x 0) k E := by
    have hk := increase ((h.glide hp.hv hp.hQ _ hh).primal D) (show k ≤ 2*k by unfold k; linarith [hp.prices]) le_rfl
    unfold intensity; rw [pow_zero,mul_one,sub_eq_add_neg A 1]
    exact paid_mul (paid_add h.relented (spent_neg (one_pay ..))) hk hp.prices.le (by linarith [h.fuel]) h.disc
  unfold joint; apply (abs_sum_le_sum_abs ..).trans
  apply le_trans (b:=∑ _j : G.ColorIndex,E) _ (le_of_eq (by simp [E]))
  apply sum_le_sum; intro j _; unfold localBase lact
  have hk x (hh : x∈Set.uIoc (0:ℝ) 1) : ‖intensity D A x 0 (v,j) (v,j)‖ ≤ E := by
    rw [Set.uIoc_of_le zero_le_one] at hh; exact only_price (he _ (Set.Ioc_subset_Icc_self hh)).1 hp.prices.le (v,j) (v,j)
  simpa only [sub_zero,abs_one,mul_one,Real.norm_eq_abs] using! intervalIntegral.norm_integral_le_of_norm_le_const hk

def pulseHead (η r Q E : ℝ) (m B : ℕ) := (payE η r Q m + (Q+1)*(payE η r Q m)^2) * ((ballCost (B+2):ℝ) * m * E)

private lemma mass {ι : Type*} [Fintype ι] (f : ι → Site c) (M : Matrix ι ι ℝ) {n C : ℝ} (hp : 0≤C)
    (ht : ∀ i j, |M i j| ≤ C) (hh : Fintype.card ι ≤ n) : Rows f f M 0 (n*C) := by
  intro i; simp only [wt,zero_mul,Real.exp_zero,one_mul]
  have he := sum_le_sum (s:=univ) (fun j _ => ht i j)
  simp only [sum_const,nsmul_eq_mul, card_univ] at he; exact he.trans (mul_le_mul_of_nonneg_right hh hp)

private lemma patch_gap (hp : Torch η r Q) (h : Allow A (along S) m η r Q) (hz : Allow Z (along S) m η r Q)
    (s : ℝ) (hh : s∈Set.Icc (0:ℝ) 1) (v : Tubular f G) (E : ℝ) (hn : 0≤E)
    (hg : ∀ i∈D.take v,∀ j∈D.take v, |A i j-Z i j| ≤ E) :
      |intensity D A s 0 v v - intensity D Z s 0 v v| ≤ pulseHead η r Q E m B := by
  let U := D.take v; let e := Embedding.subtype (·∈U)
  let f (M : Itinerary.Mat _ G) := Batch.principal U (M-1)
  let g (M : Itinerary.Mat _ G) := Batch.principal U (glide M s)
  let u := (along S) ∘ e
  let Δ := (ballCost (B+2):ℝ)*m; let d := Δ*E; let C := payE η r Q m
  have hu : Fintype.card (↥U) ≤ Δ := by
    have he := h.census; unfold Δ; rw [Fintype.card_coe]; norm_cast
    apply le_trans (Finset.card_le_card (show U⊆withinH (along S) (along S v) (B+2) from
      fun i hi => (joins ..).mpr ((separation_comm ..).trans_le (D.high i v hi)))) (Census.count_near he _ _)
  have hX := (h.glide hp.hv hp.hQ s hh).sub e
  have hZ := (hz.glide hp.hv hp.hQ s hh).sub e
  have hs : (g Z)⁻¹-(g A)⁻¹=(g Z)⁻¹ * (g A-g Z) * (g A)⁻¹ := by
    have hp : g A*(g A)⁻¹=1 := hX.initial.1
    have he : (g Z)⁻¹*g Z=1 := hZ.initial.2.1
    rw [mul_sub,sub_mul,he, one_mul,mul_assoc,hp,mul_one]
  have hx i j : (f A-f Z) i j = A (e i) (e j)-Z (e i) (e j) := by dsimp only [f, Batch.principal,e]; simp only [Matrix.sub_apply,submatrix_apply,Embedding.subtype_apply]; ring
  have hc : Rows u u (f A-f Z) 0 d := mass u _ hn (fun i j => by rw [hx]; exact hg _ i.property _ j.property) hu
  have hy : Rows u u (g A-g Z) 0 d := by
    refine mass u _ hn (fun i j => ?_) hu
    have ht : (g A-g Z) i j=s*((f A-f Z) i j) := by
      unfold f g glide Batch.principal; simp only [Matrix.submatrix_apply, Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply, smul_eq_mul]; ring
    rw [ht,hx,abs_mul,abs_of_nonneg hh.1]
    exact (mul_le_mul hh.2 (hg _ i.property _ j.property) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hC : 0 ≤ C := h.disc
  have he : 0 ≤ d := by unfold d Δ; positivity
  have hM : Rows u u (g A)⁻¹ 0 C := pricing hX.flatup.1 hp.prices.le le_rfl
  have hN : Rows u u (g Z)⁻¹ 0 C := pricing hZ.flatup.1 hp.prices.le le_rfl
  have h₁ : Rows u u ((g Z)⁻¹-(g A)⁻¹) 0 (C*d*C) := hs.symm ▸ ((hN.multiply le_rfl hy he).multiply le_rfl hM hC)
  have h₂ : Rows u u (f Z) 0 (Q+1) := by
    have hf : Rows (along S) (along S) (Z-1) 0 (Q+1) := by
      rw [sub_eq_add_neg]; exact (pricing hz.price hz.eta.le le_rfl).plus (spent_neg (one_pay ..)).1
    exact hf.restrict e e
  have h₃ : Rows u u (f A*(g A)⁻¹-f Z*(g Z)⁻¹) 0 (pulseHead η r Q E m B) := by
    rw [show f A*(g A)⁻¹-f Z*(g Z)⁻¹= (f A-f Z)*(g A)⁻¹+ (-1:ℝ) • (f Z*((g Z)⁻¹-(g A)⁻¹)) by rw [sub_mul,mul_sub]; module]
    refine pricing ((hc.multiply le_rfl hM hC).plus ((h₂.multiply le_rfl h₁ (by positivity)).pay _)) le_rfl ?_
    unfold pulseHead; rw [abs_neg, abs_one]; unfold C d Δ; exact le_of_eq (by ring)
  rw [perWindow A D v s (show D.take v=U from rfl) (D.here v),perWindow Z D v s (show D.take v=U from rfl) (D.here v)]
  exact only_price h₃ le_rfl ⟨v,D.here v⟩ ⟨v,D.here v⟩

/-- Window cost for all colors, on patches where hoof chosen from the real
D. Apply with uniform E after gauge comparison. -/
lemma patch_cost (hp : Torch η r Q) (h : Allow A (along S) m η r Q) (hz : Allow Z (along S) m η r Q)
    (v : Bond f) (E : ℝ) (hn : 0 ≤ E)
    (hg : ∀ x:G.ColorIndex,∀ i∈D.take (v,x),∀ j∈D.take (v,x), |A i j-Z i j| ≤ E) :
    |joint A D v-joint Z D v| ≤ (Fintype.card G.ColorIndex:ℝ)* pulseHead η r Q E m B := by
  let P := pulseHead η r Q E m B
  have he := inside_caps A D h hp
  have ht := inside_caps Z D hz hp
  unfold joint; rw [← sum_sub_distrib]; apply (abs_sum_le_sum_abs ..).trans
  apply le_trans (b:=∑ _j:G.ColorIndex,P) _ (le_of_eq (by simp [P])); apply sum_le_sum; intro j _
  unfold localBase lact
  rw [← intervalIntegral.integral_sub ((continuousOn_pi.mp (continuousOn_pi.mp he _) _).intervalIntegrable)
    ((continuousOn_pi.mp (continuousOn_pi.mp ht _) _).intervalIntegrable)]
  have hh x (hk : x∈ Set.uIoc (0:ℝ) 1) : ‖intensity D A x 0 (v,j) (v,j)-intensity D Z x 0 (v,j) (v,j)‖ ≤ P := by
    rw [Set.uIoc_of_le zero_le_one] at hk
    exact patch_gap D hp h hz x (Set.Ioc_subset_Icc_self hk) _ _ hn (hg j)
  simpa only [sub_zero,abs_one,mul_one,Real.norm_eq_abs] using! intervalIntegral.norm_integral_le_of_norm_le_const hh
end YM.ConnectedActivityE6.Pulse.Batch
