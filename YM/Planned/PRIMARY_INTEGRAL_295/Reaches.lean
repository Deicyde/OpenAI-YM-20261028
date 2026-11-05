import YM.Planned.PRIMARY_INTEGRAL_295.Ramble
import YM.Planned.PRIMARY_INTEGRAL_295.Throat


/-!
# Comparing true predicted probe path near origin through torus splice

qP Input log `b` from a common β with b=y‐path extension about origin.
Match on all required near cover directions; prove price of cutoff tail
error into `Earth` under the stationarity stamps.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Ramble
open Function Filter Set Metric Labels Lattice RG Wilson Source Source.Drops
open Place Streets Bazaars Postcards PPX Carrier Precision Exterior Bloch Laurent Next.Free
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
open Push.Local (Probe)
variable {d k l n : ℕ} {G : Gauge} {c f : Side} {S : StepData c f} {T : Finset Cover}
variable (Z : Probe G d) (H : Hol G)

/-- Path sampler. Genuine canonical torus identities on the entire
lift around 0 (or prove from patch gauge at start). -/
def FacePrice (b : ℝ→Dir G c) (χ : ℕ) (t θ : ℝ) : Prop :=
    ∀ x : Cover, size x ≤ χ → lift (wrap c x)=x ∧
      ∀ i : Axis, (fun y => t • b y (wrap c x, Exterior.coord i)) =ᶠ[𝓝 (0:ℝ)] fun y=>
         G.plog (G.mat (H.testLinks d 0 (θ • Z.1) y (wrap c x,i)))

private lemma pearl {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : ℝ→E} (L:E→L[ℝ] F) (hv:ContDiffAt ℝ n v 0) : L (iteratedDeriv n v 0)=iteratedDeriv n (L∘v) 0 := by
  change _=iteratedFDeriv ℝ n (L∘v) 0 (fun _=>1)
  rw [L.iteratedFDeriv_comp_left hv le_rfl]; rfl

lemma FacePrice.feeling {b:ℝ→Dir G c} {χ t θ} (ht : 0<t) (h:FacePrice Z H b χ t θ) (hv:ContDiffAt ℝ n b 0) (x : Cover)
    (hx:size x≤χ) : aboard G c (iteratedDeriv n b 0) x=lamina Z n t θ x := by
  obtain ⟨hq,h⟩:=h x hx
  funext i; let P : Dir G c→L[ℝ] G.Color:= ContinuousLinearMap.proj (wrap c x,Exterior.coord i)
  change P (iteratedDeriv n b 0)=iteratedDeriv n (script Z t θ x i) 0
  rw [pearl P hv]; apply EventuallyEq.iteratedDeriv_eq; filter_upwards [h i] with y hy
  rw [script_truth Z H (x,i)]; apply (smul_right_injective _ ht.ne'); simp only [smul_inv_smul₀ ht.ne'];
  simp only [Hol.testLinks,sub_zero,hq] at hy; exact hy

section
variable (T)
private lemma perAxis (π σ C:ℝ) (hπ:1≤π) (hσ:0<σ) (hC:0≤C) (n:ℕ) (hn:n≤ Z.2.val) :
    ∃ D:ℝ,0≤D ∧ ∀ c f (S:StepData c f) (W : Lines S.ratio.count) (v : ℝ→Dir G c)
      (t θ B : ℝ) (χ : ℕ), Blend π t θ → W.strip σ C → FacePrice Z H v χ t θ → 0≤B →
      ContDiffAt ℝ n v 0 → ‖iteratedFDeriv ℝ n v 0‖ ≤ B →
        ‖iteratedFDeriv ℝ n (earth T S W ∘ v) 0 - iteratedFDeriv ℝ n (forecast T Z W θ t) 0‖ ≤
           D*(1+B)*Real.exp (-(σ/2)*χ) := by
  obtain ⟨C',hc',hy⟩:= gathered Z π hπ n
  let r:=d*n; let P:=Throat.stomach T r σ C; have hP : 0≤P:= Throat.stoop T r hσ hC
  refine ⟨(1+C')*P,by positivity,fun c f S W v t θ B χ hb hh hv hB hx hN=>?_⟩
  let q:= earth T S W ∘ v; let Q:= forecast T Z W θ t
  have hq : ContDiffAt ℝ n q 0 := (earth T S W).contDiff.contDiffAt.comp _ hx
  have hW : Whole W:=⟨_,_,hσ,hh⟩
  have hQ : ContDiffAt ℝ n Q 0 := (forecast_truth T Z W θ t hW).contDiffAt.of_le le_top
  obtain ⟨hf,hg⟩:= hy θ t hb; let y:= iteratedDeriv n v (0:ℝ)
  have hY : Carries (aboard G c y) r B := by
    have he : ‖y‖≤B:= by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hN; exact hN
    exact ⟨hB,fun z i=> (norm_le_pi_norm y (wrap c z,Exterior.coord i)).trans (he.trans (le_mul_of_one_le_right hB (liftCost_ge ..)))⟩
  have hd:n≤d:=hn.trans (Nat.le_of_lt_succ Z.2.isLt)
  change ‖iteratedFDeriv ℝ n q 0 - iteratedFDeriv ℝ n Q 0‖≤_
  rw [← iteratedFDeriv_sub_apply hq hQ,norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_sub hq hQ]; unfold Q q
  rw [hg T W hd hW,← pearl _ hx,on_torus T S hW]; apply (Throat.tribes T W hσ hC hh r χ hY hf _).trans
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    change (B+C')*P ≤ (1+C')*P*(1+B)
    rw [mul_right_comm]; apply mul_le_mul_of_nonneg_right _ hP; nlinarith
  intro x hx'; exact FacePrice.feeling Z H hb.fine hv hx _ hx'

/-- Pre-L per row (given W prerequisite width σ and C). Card contours included.
Test may pay tighter because W actually also carries 1/L. -/
theorem billFor (π σ C:ℝ) (hπ:1≤π) (hσ:0<σ) (hC:0≤C) : ∃ D:ℝ,0≤D ∧ ∀ c f (S:StepData c f)
    (W: Lines S.ratio.count) (v:ℝ→Dir G c) (t θ B:ℝ) (χ:ℕ), Blend π t θ → W.strip σ C →
       FacePrice Z H v χ t θ → ContDiffAt ℝ (Z.2.val:WithTop ℕ∞) v 0 → Oval.Envelope 0 Z.2.val v B →
          Oval.Fuzz 0 Z.2.val (earth T S W ∘ v) (forecast T Z W θ t) (D*(1+B)*Real.exp (-(σ/2)*χ)) := by
  classical
  choose! D hD hd using fun n=> perAxis T Z H π σ C hπ hσ hC n
  let A:=Finset.range (Z.2.val+1); let B:=∑ i∈A,D i
  have ht i (hi:i∈A):= Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hh : 0≤B:=Finset.sum_nonneg fun i hi=>hD _ (ht i hi)
  refine ⟨B,hh,fun c f S W v t θ z χ hp hx hy hs hz=>?_⟩
  have he:=hz.1; refine ⟨by positivity,fun n hn=> ?_⟩
  apply (hd n hn c f S W v t θ z χ hp hx hy he (hs.of_le (Nat.cast_le.mpr hn)) (hz.2 n hn)).trans
  gcongr; exact Finset.single_le_sum (fun i hi=> hD _ (ht _ hi)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
end
end YM.Planned.PrimaryIntegral295.Ramble
