import YM.Further.LOCAL_LOG_JETS.Series
import YM.PhysicalNext.ORDERED_AFFINE_2B.Pay
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Oriole
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Garter
import YM.Push.BETA_TRANSPORT.Score
import YM.Push.STRESS_FLUX.Rebate
import YM.UVNext.PRICED_KERNELS.Shield

/-! # Total Price and interior RIGHT marker precision. Boundary separately.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Boulevard
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Push.Uniform Brush Blaze.Frond  Fare Lapis Metric Further.LogJets
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L : Side} {j : ℕ} {P:BudgetPoint} {p T B y J d C X t : ℝ} {f : Config G c→ℝ}
section weight
variable {W: ℕ→ Config G c→ℝ} {k:ℕ→ℝ} {A: ℕ→RegularAddress c}
abbrev sunny (P:BudgetPoint) : Set (Config G c):= {U| ∀ i: Pressure.Cell c, G.chord (faceValue U i)< P.threshold}
lemma smoky {U:Config G c} (h: U∈ sunny P) : flags P.threshold U=∅ := by
  ext i; simp only [flags_spec, Finset.notMem_empty, iff_false]; rintro ⟨a,_,ha⟩; exact (h a).not_gt ha
lemma sky (P:BudgetPoint): IsOpen (sunny P:Set (Config G c)):= by simp only [sunny, Set.setOf_forall]; exact isOpen_iInter_of_finite fun i=> isOpen_lt (show Continuous (fun V:Config G c=> G.chord (faceValue V i)) from (by unfold faceValue; fun_prop)) continuous_const -- names
lemma planetary (hp : early P A k p) (he:∀ i,0≤ k i): SumBudget k ((Fintype.card (Site c):ℝ)*p):= by
  have h:= budget_over univ _ (fun _=>p) (fun x hx=> hp x)
  simp_rw [sum_const,card_univ,nsmul_eq_mul] at h; refine budget_mono h he ?_; intro i; simp only [sum_ite_eq,mem_univ,↓reduceIte]; exact le_mul_of_one_le_right (he i) (Real.one_le_exp (mul_nonneg (headline P).exponent_pos.le (Nat.cast_nonneg _)))
lemma tiny {a:Directions G c} (h : ‖a‖ ≤ P.threshold) (o:Site c): P.dirBound o a := fun i=> ((norm_le_pi_norm a i).trans h).trans (le_mul_of_one_le_right P.threshold_pos.le (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))))
lemma enclosed (hp: ∀ i,P.Regular (A i).support (W i)) (hf: Summable k) (hk: ∀ i,P.supBounds (A i).site (A i).support (W i) (k i)) : Termwise P.order (sunny P) W:= by
  have he i (x:Config G c) (hx:x∈sunny P): Healthy P.threshold (A i).support x:= by unfold Healthy; rw [smoky hx]; simp
  refine ⟨fun i x hx=>(hp i).smooth _ (he i x hx),fun l hl=>?_⟩
  let d:= P.threshold+l.toFinset.sum (fun i=> ‖i‖)
  have hd : 0<d:= add_pos_of_pos_of_nonneg P.threshold_pos (sum_nonneg fun i _=> norm_nonneg _)
  have hu : ∀ i∈l, ‖i‖≤d:= fun i hi=> (single_le_sum (fun a _=> norm_nonneg a) (List.mem_toFinset.mpr hi)).trans (le_add_of_nonneg_left P.threshold_pos.le)
  let b:=d/P.threshold; have hb: 0<b:= div_pos hd P.threshold_pos; let Y:=l.map fun i=> b⁻¹ • i
  have hY:Y.length=l.length:= by simp [Y]
  have ht : Y.map (fun i=>b • i)=l:= by simp [Y,List.map_map,Function.comp_def,smul_smul,hb.ne']
  have hh i : ∀ j∈Y,P.dirBound (A i).site j:= by
    intro j hj; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hj; apply tiny
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hb).le]; apply le_trans (mul_le_mul_of_nonneg_left (hu _ ha) (inv_nonneg.mpr hb.le)); apply le_of_eq; unfold b; field_simp
  refine ⟨fun i=>b^Y.length*k i,hf.mul_left _,fun i x hx=> ?_⟩; rw [← ht, March.expands,norm_smul,Real.norm_of_nonneg (pow_pos hb _).le]
  exact mul_le_mul_of_nonneg_left ((hk _).2 x (he i x hx) Y (hY ▸ hl) (hh i)) (pow_nonneg hb.le _)
def throng (f:ℕ→ Config G c→ℝ) (V) := ∑' i,f i V
lemma commemorates (hp: Meadow.Budget P A W p) (U:Config G c) (hU:U∈sunny P): Push.Local.Chart P.order (Boulevard.throng W) U ∧ ∀ l: List (Directions G c),l.length ≤ P.order → (∀ i∈ l,‖i‖≤P.threshold) → ‖leftDerivs (Boulevard.throng W) l U‖ ≤ (Fintype.card (Site c):ℝ)*p:= by
  obtain ⟨k,h,hK⟩:=hp; have hp:= planetary h fun i=>(hK i).2.1; let p l (i):=leftDerivs (W i) l U
  obtain ⟨hx,hv⟩:= Termwise.smooth_exchange (sky P) (enclosed (fun i=> (hK i).1) hp.2.1 (fun i=> (hK i).2)) U hU
  refine ⟨hx,fun l hl hh=>?_⟩; unfold throng; rw [hv l hl]; have he:= budget_mono hp (g:=fun i=> ‖p l i‖) (fun i=> norm_nonneg _) (fun i=> (hK i).2.2 U (by unfold Healthy; rw [smoky hU]; simp) l hl (fun k hk=> tiny (hh k hk) (A i).site))
  exact (norm_tsum_le_tsum_norm he.2.1).trans he.2.2
end weight
section tight
abbrev stillA (f:Config G c→ℝ) (V:Config G c):= f V-f 1
variable {W: ℕ→ Config G c→ℝ} {H: Config G c→ℝ} {k:ℕ→ℝ} {A: ℕ→RegularAddress c}
variable {V:Config G c} (hV:V∈sunny P)
include hV
lemma tightens (hw: Meadow.Budget P A W p) (he:∀ V∈sunny P,f V= X-H V-Boulevard.throng W V)
   (hf:Push.Local.Chart P.order (stillA f) V) (hz:∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l, ‖i‖≤P.threshold) → ‖leftDerivs (stillA f) l V‖ ≤y) :
    ∀ l:List (Directions G c), l.length ≤ P.order → (∀ i∈l, ‖i‖≤P.threshold) → ‖leftDerivs (stillA H) l V‖ ≤ y + 2*((Fintype.card (Site c):ℝ)*p):= by
  have hF:(1:Config G c)∈sunny P:= fun i=> by simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using P.threshold_pos
  let p':=(Fintype.card (Site c):ℝ)*p; let t:=Boulevard.throng W
  let u (_:Config G c):= t 1
  have ht : stillA H=ᶠ[𝓝 V] (u-t)-(stillA f) := by filter_upwards [(sky P).mem_nhds hV] with k hk; change H k-H 1=(t 1-t k)-(f k-f 1); rw [he k hk,he 1 hF]; unfold t; ring
  intro l hl hh
  obtain ⟨h',hy⟩:= commemorates hw V hV; have h1 : ‖t 1‖≤ p':= (commemorates hw 1 hF).2 [] (Nat.zero_le _) (by simp)
  have hr : Push.Local.Chart P.order u V:= contDiffAt_const
  rw [(UVNext.PricedKernels.left_congr ht l).self_of_nhds, VerifiedReset.left_sub (show Push.Local.Chart P.order (u-t) V from hr.sub (g:=t∘increment V) h') hf hl, VerifiedReset.left_sub hr (show Push.Local.Chart P.order t V from h') hl]; have h : ‖leftDerivs u l V‖≤‖t 1‖:= by cases l <;> simp only [u,Work.G07.left_const]; all_goals simp -- edit lhs
  exact ((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (h.trans h1) (hy l hl hh))) (hz _ hl hh))).trans_eq (by change _=y+ 2*p'; ring)
end tight
end YM.PhysicalNext.Repeat.Boulevard
