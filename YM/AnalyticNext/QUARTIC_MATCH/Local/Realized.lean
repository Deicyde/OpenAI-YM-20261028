import YM.AnalyticNext.QUARTIC_MATCH.Cells.Entry
import YM.AnalyticNext.QUARTIC_MATCH.Local.Powered

/-!
# Widths at pre-L radii, current residuals

On-shell of THAT action. Provides tests as the norm of actual finite
coefficient arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered Tree
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain Premium Evoke Budget
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Wages
open Green (wt)
open Tracks

section norm
variable {G : Gauge} {c : Side} {n : ℕ}

def Alive (w : Fin n) (f : Dir G c →ℝ) (η C : ℝ) := ∀ x : Fin n → Cell (Per c), ∀ z : Fin n→ G.Color,
    span η (x w).1 (fun i => (x i).1) * |iteratedFDeriv ℝ n f 0 (fun i => sparse (x i) (z i))| ≤ C*∏ i, ‖z i‖
theorem Alive.less {w : Fin n} {η C} {f g : Dir G c→ℝ} (h : Alive w f η C) (hh : f =ᶠ[𝓝 0] g) : Alive w g η C := by
  unfold Alive at *; rw [← (hh.iteratedFDeriv ℝ n).eq_of_nhds]; exact h
theorem Alive.earns {w : Fin n} {η C D} {f : Dir G c→ℝ} (h : Alive w f η C) (hh : C≤D) : Alive w f η D := fun x z =>
    (h x z).trans (mul_le_mul_of_nonneg_right hh (by positivity))

theorem Alive.gives {w : Fin n} {η A B} {f g : Dir G c →ℝ} (h : Alive w f η A) (he : Alive w g η B)
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (hη : 0<η) (hp : 0 ≤ A+B)
    (hc : Colorwise (Tensor.coeff (f-g) n 0)) : Spatial (entries _ hc) (η/4) ((n.factorial:ℝ)⁻¹*(A+B)) := by
  refine ⟨by positivity, mul_nonneg (by positivity) hp,?_⟩
  intro x i j
  change ‖(entries _ hc x).val‖ ≤ _
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro z; rw [Real.norm_eq_abs,entries_eval]
  let v k := sparse (x k) (z k); let p (f : Dir G c→ℝ) := iteratedFDeriv ℝ n f 0 v
  let s := span η (x w).1 (fun i => (x i).1)
  have ht : s* |p f-p g| ≤ (A+B)*∏ i, ‖z i‖ := ((mul_le_mul_of_nonneg_left (abs_sub ..) (span_pos ..).le)).trans (by rw [mul_add]; exact (add_le_add (h x z) (he x z)).trans_eq (add_mul ..).symm)
  let b := η/4* size (lift ((x i).1-(x j).1))
  have hL : Real.exp b * |p f-p g| ≤ (A+B)*∏ i, ‖z i‖ := by
    have hb : b ≤ η*separation (x i).1 (x j).1 := by
      unfold b; have he := mul_le_mul_of_nonneg_left (show ↑(size (lift ((x i).1-(x j).1))) ≤ 4*(separation (x i).1 (x j).1:ℝ) by exact_mod_cast inhabits ..) (show 0≤η from hη.le); linarith
    have hv := Real.exp_monotone hb; apply le_trans _ ht; exact mul_le_mul_of_nonneg_right
      (hv.trans (pass_pair hη.le (x w).1 (fun i => (x i).1) i j)) (abs_nonneg _)
  unfold Tensor.coeff; rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top),show -_ * _=(-b) from by unfold b; ring]
  change |(n.factorial:ℝ)⁻¹*(p f-p g)| ≤ _
  rw [abs_mul,abs_of_nonneg (by positivity),Real.exp_neg]
  have hu := mul_le_mul_of_nonneg_left ((le_div_iff₀ (Real.exp_pos b)).mpr ((mul_comm ..).trans_le hL))
    (show 0 ≤ (n.factorial:ℝ)⁻¹ by positivity)
  exact hu.trans_eq (by ring)
end norm

section tertiary
variable (G : Gauge) (j : ℕ) (D u κ η C a : ℝ) (hp : 0<u) (he : boom u ≤ η) (hκ : 0<κ) (ha : 0<a)
include hp he hκ ha



lemma buys4 (hK : u ≤ Tracks.purchase j a η C κ) : ∃ R : ℝ,0 ≤ R ∧ ∀ (c f : Side) (S : StepData c f) (p : Clip) (W : PathData G) (θ : S.Choices) (σ τ K Λ R3 R4 : ℝ),
      S.patch.J=j → S.kernel.penalty=κ → S.patch.Branches S.kernel G → W.Bounds p τ K Λ → Rotate.Led W S.patch.L 4 (boom u) σ D R3 R4 →
        ∀ U : Cross S.ratio.count (TypeFace 1) (TypeFace 1),Evoke.motion S U η C → ∀ H H' : Bed, Attached H W → Sworn H f G → Floor H p f a C → H.metric.strip η C →
        Inputs S (installed S.ratio U) (H.metric.acts f) (H'.metric.acts c) →
          ∀ T : Forest S.ratio,Comptroller T H p W → ∀ e,0<e → PriceGap T p W e → ∀ b : Dir G c→AxisChart G T, Critical T p W b →
          Alive (0:Fin 4) (Joint.value T θ p W b) (rate u) (R*(assistance S.patch.L R3 R4+assistance S.patch.L R3 0^2)) := by
  obtain ⟨R,hR,H⟩ := pure_path G 4 4 j le_rfl le_rfl u D κ η C hp he hκ
  obtain ⟨Z,hZ,HZ⟩ := exchanged G j hp he hκ D ha hK
  refine ⟨max R (3*Z),hR.trans (le_max_left ..),?_⟩
  intro c f S p W θ σ τ K Λ R3 R4 hj hκ' hB hW hl U hU M M' ht hs hM hK' hI T hc e he' hF b hb
  obtain ⟨X,hX,hα,hβ,hCo,hθ⟩ := procure S ha hM hW hb ht hs θ hB hI hc he' hF
  apply Alive.less _ hθ
  intro x z
  let L i := sparse (x i) (z i); let X' i := (x i).1
  let F := cash S θ p W; let t (i) := tangent X 0 (L i)
  let l := S.patch.L; let c3 := assistance l R3 0; let c4 := assistance l R3 R4
  have hp : 0 ≤ c4 := zero_le_one.trans (cost_support hl)
  have hP (k) : external (installed S.ratio U) (x k) (z k)=t k := by unfold t tangent; rw [hβ]; rfl
  let K' := D4 F 0 (t 0) (t 1) (t 2) (t 3); let V i j k := leg F 0 (t i) (t j) (D2 X 0 (L 0) (L k))
  have hx : iteratedFDeriv ℝ 4 (F ∘ arc X) 0 L = K'+V 2 3 1+V 1 3 2+V 1 2 3 := by
    calc
      _ = iteratedFDeriv ℝ 4 (F ∘ arc X) 0 ![L 0,L 1,L 2,L 3] := by apply congr_arg; ext1 i; fin_cases i <;> rfl
      _ = D4 (F ∘ arc X) 0 (L 0) (L 1) (L 2) (L 3) := D4_jet ..
      _ = _ := by rw [hα.exchange]; rw [show arc X 0=0 from Prod.ext rfl hX]
  let t' := rate u; let Q := span t' (x 0).1 X'; let v := ∏ i, ‖z i‖; let D' := Z*c3^2
  have ha i j k : wt t' (X' 0) (X' k)*(wt t' (X' 0) (X' i)*wt t' (X' 0) (X' j))* |V i j k| ≤ D'*‖z 0‖*‖z k‖*‖z i‖*‖z j‖ :=
    HZ _ _ S p W θ σ _ _ _ _ hj hκ' hB hW (Rotate.led_lower hl (by exact (booms ‹0<u›).le)) U M hU hK' ht hs hM X hX hα hβ hCo
       (x 0,z 0) (x k,z k) (x i,z i) (x j,z j)
  let w i := wt t' (X' 0) (X' i)
  have hG : Q=w 1 * w 2 * w 3 := by
    unfold Q span; simp only [Fin.prod_univ_four,Green.wt]
    have hw : X' 0=(x 0).1 := rfl
    unfold w; simp [hw,Green.wt]
  have hv : v=‖z 0‖*‖z 1‖*‖z 2‖*‖z 3‖ := Fin.prod_univ_four ..
  have hb' : Q* |K'| ≤ R*c4*v := by
    have hx := H _ _ S p W θ σ τ K Λ _ _ hj hκ' hB hW hl U hU x z 0
    rw [funext hP, show iteratedFDeriv ℝ 4 F 0 t=_ from (show iteratedFDeriv ℝ 4 F 0 t=K' by unfold K'; rw [← D4_jet]; apply congr_arg; ext1 i; fin_cases i <;> rfl)] at hx
    exact hx
  have hV : Q * |V 2 3 1| ≤ D'*v ∧ Q* |V 1 3 2| ≤ D'*v ∧ Q * |V 1 2 3| ≤ D'*v := by
    rw [hG,hv];
    have h₁ : w 1*(w 2*w 3)*_ ≤ _ := ha 2 3 1; have h₂ : w 2*(w 1*w 3)*_ ≤ _ := ha 1 3 2; have h₃ : w 3*(w 1*w 2)*_ ≤ _ := ha 1 2 3
    constructor; · linarith only [h₁]
    constructor; · linarith only [h₂]
    linarith only [h₃]
  change Q* |iteratedFDeriv ℝ 4 _ _ L| ≤ _
  rw [hx];
  have he : |K'+V 2 3 1+V 1 3 2+V 1 2 3| ≤ |K'| + |V 2 3 1| + |V 1 3 2| + |V 1 2 3| := (abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)) le_rfl)
  apply ((mul_le_mul_of_nonneg_left he (span_pos ..).le)).trans
  simp_rw [mul_add]
  apply (add_le_add (add_le_add (add_le_add hb' hV.1) hV.2.1) hV.2.2).trans
  change R*c4*v+D'*v+D'*v+D'*v ≤ (_*_ +_*_)*v
  apply (le_trans _ (mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right (le_max_left ..) hp)
    (mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _))) (show 0 ≤ v from Finset.prod_nonneg fun i _ => norm_nonneg _)))
  unfold D'; linarith
end tertiary
end Wages
end YM.AnalyticNext.QuarticMatch.Local
