import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Helices
/-!
# Bound rescaled moments from E6 uniform income (Burn full F and S)
 All any port X, comparing without detaching denominator from V frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {W : ℝ}
variable {O : ChartRatio G} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f} {E : Type} {j Z m : ℕ} {M B B' K' η r t p c' : ℝ}
local notation "Y" => Air f G
local notation "φ" => facescale (univ : Finset (Bond f))
local notation "X" => F.Slice G × Y

variable (A : Coat T F) (h : Rotator P L η r M B A)
local notation "ω'" => (Measure.prod (F.order G) A.dice)
local notation "Q₀" => A.relating

def growF (j:ℕ) (x:X):= (φ x.2)^j

lemma fitHS (hz:Y) (hc : 1/2 ≤ c') : φ (c'⁻¹ • hz) ≤ 2*φ hz := by
  unfold facescale; simp_rw [show ∀ i:Tubular f G,(c'⁻¹ • hz).ofLp i=c'⁻¹ * hz.ofLp i from fun _=>rfl,abs_mul,← mul_sum]; rw [abs_of_nonneg (by positivity : 0 ≤ c'⁻¹)]
  let X':= univ (α:=Bond f); let G' := ∑ i∈lensS X' G, |hz.ofLp i|; have he:0≤G':=sum_nonneg fun _ _=>abs_nonneg _; have hp:c'⁻¹≤2:= by apply (inv_le_iff_one_le_mul₀ (show 0<c' by linarith)).mpr; linarith
  linarith [mul_le_mul_of_nonneg_right hp he,Nat.cast_nonneg (α:=ℝ) X'.card, Nat.cast_nonneg (α:=ℝ) (lensS X' G).card]

def cargo (G : Gauge) (L f : Side) (η r Q:ℝ) (j : ℕ) :=
    let A := Finset.univ (α:=Bond f); let c:ℝ:=(lensS A G).card; let Y':=1+(A.card:ℝ)+c+c
    Y'^j*(1+c*(2*Real.exp (payE η r Q (tubularPrice G L)*(j:ℝ)^2/2)))
include h
lemma ingot (j:ℕ) : let P(x:X):=(φ x.2)^j
    Integrable P (ω') ∧ ∫ x,P x ∂ω' ≤ cargo G L f η r M j := by
  intro P; obtain ⟨hk,hp⟩ := globes univ h j
  have hv : Integrable P (ω'):= hk.comp_snd _
  refine ⟨hv,?_⟩; rw [integral_prod _ hv]; unfold P; simp; exact hp
variable (j : ℕ) (ha : 0<c') (ht:t≤1/4) (hk : |c'^2-1| ≤ t)
local notation "v" => cargo G L f η r M
local notation "w" => walk (Q₀) c'
local notation "K" => massQ G f L η r M
include ha ht hk
lemma hearth : let p(x:X):= w x.2* growF j x
      Integrable p (ω') ∧ ∫ x,p x ∂ω' ≤ 2^j*v j := by
  intro f; let p (x:X):=(φ (c'⁻¹ • x.2))^j
  obtain ⟨hf,hq⟩ := ingot A h j
  have hs x:p x≤2^j*growF j x := (pow_le_pow_left₀ (zero_le_one.trans (Flux.expenses ..).1) (fitHS x.2 (logC ha ht hk).1) j).trans_eq (mul_pow ..)
  have hx : Integrable p (ω'):= (hf.const_mul (2^j)).mono' (by unfold p facescale; fun_prop) (ae_of_all _ fun x=> by rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans (Flux.expenses ..).1) j)]; exact hs x)
  obtain ⟨he,hh⟩:= earningsK (μ:=F.order G) _ h.fullC ha p
  have hz : f=(fun x:X=> w x.2 • p (x.1,c' • x.2)) := by funext x; unfold f p growF; rw [show c'⁻¹ • _=x.2 from inv_smul_smul₀ ha.ne' x.2]; rfl
  rw [hz]; refine ⟨hh.1 hx,?_⟩; apply he.symm.trans_le; apply (integral_mono hx (hf.const_mul (2^j)) hs).trans; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hq (by positivity)
lemma amplitude :
    let f (x:X):= |w x.2-1| * growF j x
    Integrable f (ω') ∧ ∫ x,f x ∂ω' ≤ t*K * (v (j+2)+2^(j+2)*v (j+2)):= by
  intro f; have hp := (abs_nonneg _).trans hk
  let u (x:X):= (1+ w x.2) * growF (j+2) x; have hW x:0< walk A.relating c' x:= bristle _ _ ha x
  have h: 0 ≤ K := by unfold massQ lunar warpK; have hp := (ups A h).disc; have hp: 0 ≤ warpK G L η r M:=hp; unfold warpK at *; positivity
  let k:=t* K; have hk':0 ≤ k:= mul_nonneg hp h
  obtain ⟨hu,hq⟩:= hearth A (by assumption) (j+2) ha ht hk
  obtain ⟨hr,hz⟩:= ingot A (by assumption) (j+2) -- edit implicit conflict
  have he : u=(growF (j+2):X→ℝ)+(fun x=> walk A.relating c' x.2*growF (j+2) x):= funext fun i=> by unfold u; simp [add_mul]
  have hU : Integrable u (ω') := he.symm ▸ hr.add hu
  have hx x:f x≤ k*u x := by
    have ht':0≤ growF j (x:X):=pow_nonneg (zero_le_one.trans (Flux.expenses ..).1) _
    apply (mul_le_mul_of_nonneg_right ((log_peak_A (hW x.2)).trans (mul_le_mul_of_nonneg_right (walksWorth A (by assumption) ha ht hk) (add_pos (hW x.2) zero_lt_one).le)) ht').trans_eq
    unfold k u growF; rw [pow_add]; ring
  have hb x : 0 ≤ f x:= mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans (Flux.expenses ..).1) _)
  have hF : Integrable f (ω'):= (hU.const_mul k).mono' (?_ : AEStronglyMeasurable f (ω')) (ae_of_all _ (fun x=> by rw [Real.norm_of_nonneg (hb x)]; exact hx x))
  swap
  · have hv:= show Measurable (fun z:X=> walk A.relating c' z.2) from (rated A.relating c').comp measurable_snd
    unfold f growF facescale; fun_prop (disch:=assumption)
  refine ⟨hF, (integral_mono hF (hU.const_mul k) hx).trans ?_⟩; rw [integral_const_mul,he,integral_add' (show Integrable (growF (j+2)) (ω') from hr) hu]; exact mul_le_mul_of_nonneg_left (add_le_add hz hq) hk'
end YM.PhysicalNext.Repeat.Alabaster
