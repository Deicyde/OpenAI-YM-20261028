import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Loom
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Spindle
/-! # Clocked forced and unforced levelMean/emerging. Actual common Air marginal.
 κ exposures on unit level exponential enough even varying estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open AnalyticBridge VerifiedReset Quotes Extra.Iteration
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ} {x d μ C : ℝ} {F : Forest S.ratio}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f} (H : Cash W x μ L Q o C T R)
lemma accused (H : Facing R I) (d p':ℕ): areas R T d p'=areas I T d p':= by
  unfold areas footprints; rw [show Raw.forcedFoot S.ratio d p' R=Raw.forcedFoot S.ratio d p' I from funext (pointed H _ _),roadway,roadway, location H]
lemma accusedS (H : Facing R I) (z : Molecule S) (p d:ℕ) : troupe T R p d z = troupe T I p d z:= by
  unfold troupe Contract.sealed Contract.incidence; rw [H.forced]
lemma accusedP (H : Facing R I) (X : Coat T F) (z : Molecule S) (p:ℕ) : standsIn X R p z=standsIn X I p z:= by unfold standsIn claimed ground; rw [accused H,accusedS H]

include H
variable (Vp : Covers T x H)
include Vp
lemma venerated : ∃ K : ℝ,0 ≤ K∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t →0<t→ t ≤ 1→ t≤ R.beta/2→ ∃ g:Molecule S →ℝ, SumBudget g K ∧∀ (F:Forest S.ratio) (X:Coat T F), X.width=o.K→X.x=x→X.manifest→∀ p l Z,
    let J:=X.vertex I Q.table W o.a l Q.halo (low R I • Z)
    let A:=X.vertex R Q.table W o.a l Q.halo Z
    |∏ i∈p,J i| ≤ g p ∧ |(∏ i∈p,J i)-(∏ i∈p,A i)|≤ t*g p := by
  obtain ⟨K,hK,hx⟩:= cornice H Vp
  let k:= ∑' i,H.fair i
  refine ⟨Real.exp (3*3^(0:ℕ)*(k+K)),Real.exp_nonneg _,?_⟩; intro I a b t hp ht hE hA; obtain ⟨f₀,hF,h⟩:=hx I a b t hp hE hA
  let v i:= H.fair i+f₀ i/t; let A i:= 3*(3:ℝ)^(0:ℕ)*v i; have hv : SumBudget H.fair k:= ⟨H.fair_price,pertinent H,le_rfl⟩
  refine ⟨fun p=>∏ i∈p,A i,insured _ _ _ 0 hv hF ht,?_⟩; intro F X hy hw hM p l Z J A'
  let J' i (_:ℝ):= J i; let a i (_:ℝ):= A' i
  obtain ⟨hz,hx⟩:= walks (n:=0) a J' v 0 p ht.le hE (fun i hi=> (Brush.certified zero_le_one _).climb (le_trans (H.voice X hw hy hM ..) (le_add_of_nonneg_right (div_nonneg (hF.1 _) ht.le))) le_rfl)
    (fun i hi=> (Brush.certified zero_le_one (J i-A' i)).climb ((h F X hy hw hM ..).trans (show f₀ i≤ t*v i from (by unfold v; rw [mul_add,mul_comm t (f₀ i/t),div_mul_cancel₀ _ ht.ne']; exact le_add_of_nonneg_left (mul_nonneg ht.le (H.fair_price i))))) le_rfl)
  exact ⟨hz.bound,hx.bound⟩
lemma meritP : ∃ K : ℝ,0 ≤ K ∧ ∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ), Equalized Q.table R I a b t→0<t→ t ≤ 1/4 → t≤ R.beta/2→∃ g:Molecule S →ℝ, SumBudget g K ∧∀ (d:ℝ) (_H': Cash W x μ L Q o d T I) (F:Forest S.ratio) (X:Coat T F), X.width=o.K→X.x=x→X.manifest→∀ p l,
       |X.attains I Q.table W o.a l Q.halo p-X.attains R Q.table W o.a l Q.halo p|≤t*g p := by
  obtain ⟨K,hK,h⟩:=venerated H Vp
  let q:= massQ G f L o.eta o.gap o.ample; let c' := cargo G L f o.eta o.gap o.ample 2; let v:=|q*(c'+2^2*c')|+1
  have hh : 0 ≤ v:= by unfold v; positivity
  refine ⟨v*K,mul_nonneg hh hK,?_⟩; intro I a b t hp ht hu he; obtain ⟨g,hg,hv⟩:= h I a b t hp ht (hu.trans (by norm_num)) he
  refine ⟨fun p=> v*g p,budget_scale hh hg,?_⟩; intro d H' F X hX hx hm p l
  let L:=low R I
  have hr:= (H.laws.data.localP F X hx hX hm).sails; let A:= X.relating; let A': F.Slice G ×Air f G→ℝ := X.body R Q.table W o.a l Q.halo p
  let D:=(X.body I Q.table W o.a l Q.halo p); let B (z:F.Slice G× Air f G):=walk A L z.2 *D (z.1,L • z.2); let μ:=(F.order G).prod X.dice
  have hh:= H'.integrated X hx hX hm l p; have H:= H.integrated X hx hX hm l p
  have hz := earningsK A hr.fullC (uplift hp.toFacing|>.2.2.1) (μ:=F.order G) D
  have hB : Integrable B μ:= hz.2.1 hh
  obtain ⟨hJ,hY⟩:= amplitude X hr 0 (uplift hp.toFacing|>.2.2.1) hu hp.heat; simp only [growF, pow_zero, mul_one,Nat.zero_add] at hJ hY
  let w (x:F.Slice G × Air f G):= |walk A L x.2-1|
  rw [show X.attains I Q.table W o.a l Q.halo p=∫ i,B i ∂μ from hz.1]; change ‖_-(∫ i,A' i ∂μ)‖≤_
  rw [← integral_sub hB (show Integrable A' μ from H)]
  apply (norm_integral_le_integral_norm _).trans ((integral_mono_ae (hB.sub (show Integrable A' μ from H)).norm (hJ.mul_const (g p)|>.add (show Integrable (fun _=> t*g p) μ from integrable_const _)) ?_).trans ?_)
  · filter_upwards with Y
    let X':= X.wrapY Y.1; let e:= D (Y.1,L • Y.2); let y := walk A L Y.2; let z:= A' Y
    obtain ⟨ha,hb⟩:= hv F X' hX hx hm p l Y.2
    change |y * e-z| ≤ |y-1| *g p+t*g p
    rw [show y * e-z=(y-1)*e+(e-z) by ring]; apply (abs_add_le ..).trans; rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _)) hb
  rw [integral_add' (hJ.mul_const (g p)) (show Integrable (fun _=> t*g p) μ from integrable_const _),integral_mul_const,integral_const]
  change _*g p+ μ.real Set.univ • _ ≤ t* (v*g p)
  rw [show μ.real Set.univ=1 from probReal_univ,one_smul]; refine (add_le_add_left (mul_le_mul_of_nonneg_right hY (hg.1 _)) (t*g p)).trans ?_; have hG:= hg.1 p; unfold v; nlinarith only [mul_le_mul_of_nonneg_left (le_abs_self (q*(c'+2^2*c'))) (mul_nonneg ht.le hG)]
lemma masterP : ∃ K:ℝ,0 ≤ K ∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→0<t→t≤1/4→t≤R.beta/2→∃ g:Molecule S→ℝ, SumBudget g K ∧ ∀ (d:ℝ) (H':Cash W x μ L Q o d T I) (F: Forest S.ratio) (X: Coat T F),X.width=o.K→X.x=x→ ∀ p:Molecule S,
   |H'.emerging X p-H.emerging X p|≤t*g p:= by
  obtain ⟨K,hK,h⟩:= meritP H Vp; refine ⟨K,hK,?_⟩; intro I a b t hp ht hE he; obtain ⟨g,hg,hP⟩:= h I a b t hp ht hE he
  refine ⟨g,hg,?_⟩; intro d H' F X hX hx p
  unfold Cash.emerging proceedsA; rw [accusedP hp.toFacing]; split
  · unfold amountP levelMean likely; let k:ℝ := Fintype.card S.Choices; have h :0<k:= by unfold k; positivity
    rw [← mul_sub, ← sum_sub_distrib,abs_mul,abs_of_nonneg (inv_pos.mpr h).le]
    apply (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum (s:=univ) (fun k _=> hP d H' F ((planted X p).taggedL k) hX hx (planted_valid X p) p (own p)))) (inv_pos.mpr h).le).trans_eq
    rw [sum_const,nsmul_eq_mul, card_univ]; exact inv_mul_cancel_left₀ h.ne' _
  rw [sub_self,abs_zero]; exact mul_nonneg ht.le (hg.1 _)
end YM.PhysicalNext.Repeat.Alabaster
