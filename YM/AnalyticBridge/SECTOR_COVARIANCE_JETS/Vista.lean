import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Twist

set_option warningAsError false

/-! Genuine window comparisons and shifted derivative currencies for the
selected precision/inverse, both transposes charged from the same subsector.
Doesn't assert that two symmetrized estimates may be inverted entrywise. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost resolve tagPrice)
open FreeResolvent.Window (Survey)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C V η u Y : ℝ}
variable {ι κ α : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] {p : ι → Site c}
  {A F : Directions G c → Matrix ι ι ℝ} {B : Directions G c} {W : ι→Set ι}

structure Vista (p : ι → Site c) (A : Directions G c → Matrix ι ι ℝ) (W : ι → Set ι) (B : Directions G c)
    (d Y C : ℝ) (k : ℕ) : Prop where
  full (u : ℝ) : 0≤u → Spiral p (action A u) B u d C k
  thin (s : Set ι) (u : ℝ) : 0≤u → Spiral (fun i:s => p i.val) (fun z => resolve (principal (A z) s) u) B u d C k
  glass (u : ℝ) : 0≤u → Spiral p (shelve W A u) B u d C k
  eject (u : ℝ) : 0≤u → RatesPaid p p d (Y*C*drain u) k (hitch W A u) B
  difference (u : ℝ) : 0≤u → RatesPaid p p d (Y*C*drain u*drain u) k (shelve W A u-action A u) B

lemma Vista.weaken (h : Vista p A W B d Y C k) {t X M : ℝ} (ht : t≤d) (hc : C≤M)
    (hX : Y*C≤X*M) : Vista p A W B t X M k := by
  refine ⟨fun u hu => (h.full u hu).less hc ht hu, fun s u hu => (h.thin s u hu).less hc ht hu,
    fun u hu => (h.glass u hu).less hc ht hu,fun u hu => ?_,fun u hu => ?_⟩
  · exact reducePay (h.eject u hu) ht (mul_le_mul_of_nonneg_right hX (drain_pos hu).le) le_rfl
  exact reducePay (h.difference u hu) ht (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX (drain_pos hu).le) (drain_pos hu).le) le_rfl

def tower (k : ℕ) (C V η : ℝ) : ℝ :=
  let N:= tallyInverse k C V η
  max (max N (V*N)) (max (unitH k C N V) (unitF k C N V))
lemma tower_nn (hv : Price σ C η d 1 V 1 k) : 0≤tower k C V η := (le_max_of_le_left (le_max_of_le_left hv.meter_abs))

lemma makeVista (h : RatesPaid p p σ C k A B) (he : Gapped (A B) η) (hv : Price σ C η d 1 V 1 k)
    (hp : (native c).Volume p d V) (hw : Bars W p n) : Vista p A W B d (rateBreak d n k) (tower k C V η) k := by
  let N := tallyInverse k C V η
  let T := tower k C V η
  have hh : N ≤ T := le_max_of_le_left (le_max_left ..)
  have hz : rateBreak d n k ≥ 0 := (Real.exp_pos _).le
  have hx u (hu : 0≤u) := editCosts W h he hv hp hu hw
  refine ⟨fun u hu => (inverseCost h he hv hp hu).less hh le_rfl hu,
    fun s u hu => (areaCost s h he hv hp hu).less hh le_rfl hu,fun u hu => ?_,fun u hu => ?_,fun u hu => ?_⟩
  · exact ((hx u hu).1).less (le_max_of_le_left (le_max_right ..)) le_rfl hu
  · exact Bundle.mono ((hx u hu).2.1) le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (le_max_of_le_right (le_max_left ..)) hz) (drain_pos hu).le)
  have ht : unitF k C N V ≤ T := le_max_of_le_right (le_max_right ..)
  exact Bundle.mono ((hx u hu).2.2) le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hz) (drain_pos hu).le) (drain_pos hu).le)

section cov
-- formulas names separate from functions on group domains
def obscure (W : ι → Set ι) (A : Directions G c → Matrix ι ι ℝ) (y : Directions G c) := clouded W (A y)
def storm (W : ι → Set ι) (A : Directions G c → Matrix ι ι ℝ) (y : Directions G c) := A y*obscure W A y-1

def evenKernel (A : Directions G c → Matrix ι ι ℝ) (y : Directions G c) := (1/2:ℝ) • (A y+(A y).transpose)
lemma obscure_even : obscure W A = evenKernel (shelve W A 0) := by
  funext B; unfold obscure evenKernel shelve; rw [zero_smul,add_zero]; rfl
lemma invertOnly (A : Directions G c → Matrix ι ι ℝ) : action A 0 = fun y => (A y)⁻¹ := by
  apply funext; intro y; change (A y+(0:ℝ) • 1)⁻¹=_; rw [zero_smul,add_zero]
omit [DecidableEq ι] in
lemma even_rates (h : RatesPaid p p σ C k A B) : RatesPaid p p σ C k (evenKernel A) B := by
  apply Bundle.mono (Bundle.scale (Bundle.one_add h (Bundle.transpose h)) (1/2:ℝ)) le_rfl
  norm_num; linarith
lemma even_sub (h : ∀ B, (A B).IsSymm) : obscure W A - action A 0 = evenKernel (shelve W A 0 - action A 0) := by
  rw [obscure_even,invertOnly]
  funext b; ext i j
  let X := shelve W A 0 b; let Q := (A b)⁻¹
  change (1/2:ℝ)*(X i j+ X j i)-Q i j= (1/2:ℝ)*((X i j-Q i j)+(X j i-Q j i))
  rw [show Q j i=Q i j from (h b).inv.apply ..]; ring

lemma Vista.evans (h : Vista p A W B d Y C k) (hc : 0≤C) (hi : ∀ B, (A B).IsSymm) :
    RatesPaid p p d C k (obscure W A) B ∧ RatesPaid p p d (Y*C) k (obscure W A-action A 0) B := by
  have hp : drain 0=1 := by simp [drain]
  refine ⟨?_,?_⟩
  · rw [obscure_even]; apply even_rates; simpa only [hp,mul_one] using ((h.glass 0 le_rfl).mild le_rfl hc)
  rw [even_sub hi]; apply even_rates; simpa only [hp,mul_one] using h.difference 0 le_rfl

-- Shrink to cost a product, keeping all derivative-position costs also
omit [DecidableEq ι] in
lemma zip_rates {C' : ℝ} (h : RatesPaid p p σ C k A B) (hf : RatesPaid p p σ C' k F B)
    (hc : 0≤C) (hC : 0≤C') (hp : 0≤d) (he : d+k*d ≤ σ) :
    RatesPaid p p d (tagPrice 1 k C C') k (fun y => A y*F y) B := by
  have hd : d≤σ := le_trans (le_add_of_nonneg_right (by positivity)) he
  exact Bundle.multiply (less_bundle h hd le_rfl) (less_bundle hf hd le_rfl) (position_move _ _ hp) hp le_rfl hc hC hp he

lemma moneyStorm (h : RatesPaid p p σ C k A B)
    (he : RatesPaid p p σ V k (obscure W A-action A 0) B)
    (hc : 0≤C) (hv : 0≤V) (hi : Gapped (A B) η) (hz : 0<η) {d : ℝ} (hp : 0≤d) (ht : d+k*d≤σ) :
    RatesPaid p p d (tagPrice 1 k C V) k (storm W A) B := by
  refine Bundle.glue (zip_rates h he hc hv hp ht) ?_
  have hn : Neat A 0 B := by unfold Neat; simpa only [zero_smul,add_zero] using (debut hi).unit_det hz
  filter_upwards [germ_valid hn h.smooth.continuousAt] with y hy
  unfold Neat at hy; rw [zero_smul,add_zero] at hy
  rw [invertOnly]; change A y*(obscure W A y - (A y)⁻¹)=A y*obscure W A y-1
  rw [Matrix.mul_sub,Matrix.mul_nonsing_inv _ hy]

lemma residualInverse (h : RatesPaid p p σ C k (storm W A) B) (hc : 0≤C)
    (hi : Gapped (obscure W A B) η) (hη : 0<η) (hh : RatesPaid p p σ V k (obscure W A) B) (hv : 0≤r)
    (he : RatesPaid p p σ r k (action (obscure W A) 0) B) (hp : 0 ≤ d) (hd : d+k*d≤σ) :
    RatesPaid p p d (tagPrice 1 k C r) k (action (obscure W A) 0-A) B := by
  have hz := zip_rates h he hc hv hp hd
  let F y := storm W A y*action (obscure W A) 0 y
  have ht : RatesPaid p p d (tagPrice 1 k C r) k (fun y => (-1:ℝ)• F y) B := by
    have ht := Bundle.scale hz (-1:ℝ); simpa only [abs_neg,abs_one,one_mul] using ht
  refine Bundle.glue ht ?_
  have hn : Neat (obscure W A) 0 B := by unfold Neat; simpa only [zero_smul,add_zero] using (debut hi).unit_det hη
  filter_upwards [germ_valid hn hh.smooth.continuousAt] with y hy
  unfold Neat at hy; rw [zero_smul,add_zero] at hy
  change (-1:ℝ)•F y=action (obscure W A) 0 y-A y
  unfold F; rw [invertOnly]
  change (-1:ℝ)• ((A y*obscure W A y - 1) * _)=(obscure W A y)⁻¹-A y
  rw [Matrix.sub_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hy, Matrix.one_mul,Matrix.mul_one,
    neg_smul,one_smul, neg_sub]
end cov
end YM.AnalyticBridge.Covariance
