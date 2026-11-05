import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter

/-! # Turning near-gauge chart price into alm Measure. No threshold derivative. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Boulevard
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.Uniform Brush Blaze.Frond  Fare Lapis Metric
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {p T B y J d C X : ℝ} {f : Config G c→ℝ}
abbrev actual (x:Positions (Uniform.Primary c G)):= represent (Uniform.tint G _ x)
variable {x:Positions (Uniform.Primary c G)}
local notation "U" => actual x
lemma seek (hd: 0<d) : ∃ Q>0,∀ a:G.Color, ‖a‖≤Q → G.plog (G.mat (G.lieExp a))=a ∧ ‖G.mat (G.lieExp a)-1‖≤d:= by
  have h' : ContinuousAt (fun v:G.Color=>‖G.mat (G.lieExp v)-1‖) 0 := by fun_prop
  have hv := h' (gt_mem_nhds (show ‖G.mat (G.lieExp 0)-1‖<d by simpa using hd))
  obtain ⟨r,hr,hx⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (G.plog_left.and hv)
  exact ⟨r,hr,fun i hi=> let h:=hx (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hi)); ⟨h.1,(show _<d from h.2).le⟩⟩
variable (S: Suitable G j J d 1) (hq : ∀ a:G.Color, ‖a‖ ≤ Uniform.shade G * p → G.plog (G.mat (G.lieExp a))=a ∧ ‖G.mat (G.lieExp a)-1‖≤d)
    (hp:0<p) (hP:‖x‖≤p)
    (h : Brush j T p⁻¹ (f∘actual) x) (hc: j.factorial*J*((1+Blaze.royalty G)*C)≤p) (hC : (1+Blaze.royalty G)*C ≤ 1)
def ticket (j:ℕ) (t:ℝ) := j.factorial*t*(1+(1+1))^j
include S hq hp hP hc hC h
lemma resources : Ore U f C (ticket j T) j:= by
  intro E _ _ _ W y hy hW
  let q:= tint G (Body 1 c)
  have hp i : ‖q x i‖≤ Uniform.shade G*p:= (norm_le_pi_norm _ _).trans ((Uniform.tint_le _).trans (mul_le_mul_of_nonneg_left hP (Uniform.shade_pos _).le))
  let f₁ (z:E):= SliceRows.toLog (G:=G) fun i:Bond c=> G.plog (G.mat (W z i)); let g z:= q.symm (f₁ z)
  have ht i: W y i=G.lieExp (q x (pole i)):= by rw [hy]; exact Work.F03.represent_link ..
  have ht' i : G.plog (G.mat (W y i))= q x (pole i):= by rw [ht]; exact (hq _ (hp _)).1
  have h' : f₁ y=q x:= by ext1 i; obtain ⟨j,rfl⟩:= (Work.E03.poleEquiv _).surjective i; change collect G (f₁ y) j=q x (pole j); unfold f₁; rw [collects]; exact ht' j -- collect
  have hg:g y=x:= q.symm_apply_eq.mpr h'
  obtain ⟨hb,_,hv⟩ := ep hW S (fun i=> by rw [ht]; exact (hq _ (hp _)).2)
  let e:= (1+Blaze.royalty G)*C
  have hQ : Brush j p 1 g y := by
    have hB := Brush.report (f:=f₁) (E:=E) hb q.symm.toContinuousLinearMap (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=> by rw [one_mul]; exact Uniform.tint_inv_le _))
    rw [one_mul] at hB; change Brush j (j.factorial*J) e g y at hB
    apply Brush.offer.mpr; refine ⟨hB.smooth,fun i hi=>?_⟩; rcases i with i|i
    · unfold normJ; rw [norm_iteratedFDeriv_zero,hg]; exact hP
    apply (hB.order _ hi).trans; apply le_trans _ hc; apply mul_le_mul_of_nonneg_left _ hB.nonneg
    have he := pow_le_pow_of_le_one hB.pos hC (by omega : 1≤ i+1); rwa [pow_one] at he
  have hx: W=ᶠ[𝓝 y] actual ∘ g:= hv.trans (Eventually.of_forall (fun i=> by change represent (f₁ i)=represent (q _); rw [show q _=f₁ i from q.apply_symm_apply _]))
  have he := Brush.trail (u:=1) (h:=‹0<p›) (show Brush j T p⁻¹ (f ∘ actual) (g y) from hg.symm ▸ h) (hQ.climb (by rw [one_mul]) le_rfl) (mul_inv_cancel₀ ‹0 < p›.ne'|>.le)
  exact Brush.shimmy he.trim (hx.fun_comp f)
variable (M : Sailor G P.threshold B j) (hB:0< B) (he : 0<C) (hm : j*B ≤ C)
include M hB he hm
lemma hires : Push.Local.Chart j f U ∧∀ l: List (Directions G c), l.length≤ j → (∀ i∈l, ‖i‖≤P.threshold)→‖leftDerivs f l U‖ ≤ticket j T:= by
  have hu:= resources S hq hp hP h hc hC -- order
  refine ⟨charted hu he,?_⟩; intro l hl hh
  let f (_:ℝ):= U; have hM:Mode f 0 j 0:=⟨le_rfl,fun i=> a_oneB G _ le_rfl⟩
  have ht:= explorers hu hM rfl (M.stroke c) l (by simpa using (mul_le_mul_of_nonneg_right (show (l.length:ℝ)≤ j from by exact_mod_cast hl) hB.le).trans hm) hh (show 0+l.length≤j by omega); exact ht.bound
end YM.PhysicalNext.Repeat.Boulevard
