import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Vault
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Glisten

/-!
# Moving Z jets up to probe n including plate and V9 Γ at actual W chart

Pay enchant via unaltered material U expiry. `Tentacle` carries tides while
 using post-L window costs on physical Ψ profiles (E6 cone ≠ V9 doors!).
 Accept prior authorization from metrics not invented bounds. Clock inputs
 for prenegate kept independent of μ,M and plate choices. No changes off region.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {p j n : ℕ} {L : Side}
variable {d A t C' w M N z β W k ε J' L₀ : ℝ}
open Planned.AtomRegular

-- product influentials all Key even if not used. s angular Ω displacement on free chart.
section support
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E→ Config G c} {x : E} (X : Coat T F)
    {I:Type} [Fintype I] [DecidableEq I] (a : Museum F X.x (bareStores S) K Y I) (h : Scrim X a)
    (s : Prices G I)

def spied : Air f G := WithLp.toLp 2 (Function.extend (scoop X a) s (fun _=>0))
set_option linter.unusedSectionVars false in
lemma inset : WithLp.ofLp (spied X a s) ∘ scoop X a=s := funext (fun j=> (scoop X a).injective.extend_apply s (fun _=>0) j)
lemma reads (i:I) : worldZ X β (spied X a s) (a.address i)=peanuts X a X.V β s i:= by
  nth_rw 2 [← inset X a s]; rfl
lemma pulses (V : Config G c) : pulse X V a s d β=∏ i, steerJ X d (worldZ X β (spied X a s)) V (a.address i):= by
  simp only [steerJ,reads]; rfl
lemma heard (V : Config G c) (i:I): steer X d (worldZ X β (spied X a s)) V (a.address i)=fawn X V a s d β i := by unfold steer; rw [reads]; rfl

lemma beep (hh : 0≤w) (hv : (Fintype.card I:ℝ) ≤ N) (hf : ∀ i, Brush n 1 w (fun y=> steerJ X d (worldZ X β (spied X a s)) (Z y) i) x) :
    Brush n ((1+N*w)^n) 1 (fun y=>pulse X (Z y) a s d β) x := by
  simp_rw [pulses]; have he:= Brush.all_prod Finset.univ _ _ _ (fun (i:I) (_:i∈Finset.univ)=> hf (a.address i))
  simp only [Finset.prod_const_one,Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at he
  simpa only [one_mul] using! (he.climb le_rfl (mul_le_mul_of_nonneg_right hv hh)).trim

variable (hh : Clutch X (spied X a s) t β M x n Z (fun y=> steer X d (worldZ X β (spied X a s)) (Z y)) (fun y=> course X d β (spied X a s) (Z y)))
lemma chalking (i:I) (hh : Clutch X (spied X a s) t β M x n Z (fun y=> steer X d (worldZ X β (spied X a s)) (Z y)) (fun y=> course X d β (spied X a s) (Z y))) : Brush n M 1
    (fun y=> fawn X (Z y) a s d β i-peanuts X a X.V β s i) x := by simp_rw [← heard,← reads (β:=β)]; exact hh.bud _
include hh
lemma geared (hb : ∀ i, Brush n C' 1 (volume6 X a i ∘ Z) x) (ha : (gStep β)⁻¹ ≤ N) (hs : ‖s‖≤ w) :
    Prism.Moves x n (fun x=>reading6 X (Z x) a s d β) (N*(M+(C'+C'))+w) := by
  intro i; let q:=i.1; let f z:= volume6 X a i.1 (Z z)-volume6 X a i.1 X.V
  have hz := (hb q).bound; rw [Function.comp_apply,hh.atV] at hz
  have hK : Brush n (C'+C') 1 f x := (hb i.1).separating ((Brush.certified zero_le_one _).climb hz le_rfl)
  have h₁ := (chalking X a s q hh).separating hK; let u x:= reading6 X (Z x) a s d β; let g:=gStep β; have hg : 0<g:= inv_pos.mpr (Real.sqrt_pos.mpr hh.beta)
  have he := h₁.smul g⁻¹
  have he' : Brush n (N*(M+(C'+C'))) 1 (fun x=> tape (u x) q-tape s q) x := by
    apply ((he.climb _ le_rfl)).shimmy
    · refine Eventually.of_forall fun x=>?_; dsimp only; rw [← to_strip X (Z x) a hh.beta s]; unfold f
      change _=g⁻¹ • ((volume6 X a q (Z x)+g • tape (u x) q- (volume6 X a q X.V+g • tape s q))- _); simp only [smul_sub,smul_add, inv_smul_smul₀ hg.ne']; abel
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hg.le)]; exact mul_le_mul_of_nonneg_right ha h₁.nonneg
  apply ((colorEvaluated i.2 he').gathering ((Brush.certified zero_le_one (s i)).climb ((norm_le_pi_norm ..).trans hs) le_rfl)).shimmy
  exact Eventually.of_forall fun x=> show u x i =_ from (sub_add_cancel ..).symm
end support
end YM.PhysicalNext.Repeat.Brim
