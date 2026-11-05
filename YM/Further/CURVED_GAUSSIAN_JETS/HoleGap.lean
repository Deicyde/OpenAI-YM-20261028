import YM.Further.CURVED_GAUSSIAN_JETS.Algebra
import YM.Further.CURVED_GAUSSIAN_JETS.LocalRows
import YM.Next.ROTATIONS.Constraints
import YM.Progress.STATIONARY_SCENES.Dispatch
import YM.Push.SECTOR_MEASURE.Presented
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk

/-!
# : fixed-L compulsory curved tangent gap in a punctured tree slice

The theorem `sector_gap` isn't a generic Löwner monotonicity assumption
on the desired Gram. Even before the D-row accounting of a sector is
supplied, this estimates the input link variables by *only* the
unweighted curved direct and rooted noise tangents at the actual copied V,
with their true analytic predictor and curved curvature projection. Need
avoidance of output flags near every active (possibly nonzero) position,
not a bound by a flat whole torus operator on a single gauge image of V.
Ignore all remaining (ell etc) rows for this lower estimate. A use in
Funding below on arbitrary row lists with explicit Covers and bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Pockets
open Function Filter Set Metric Gauge Lattice Tree Wilson RG Precision Work Exterior Pressure Bid Next.Fluctuations
open Matrix
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def Paid (S : StepData c f) (G : Gauge) := Larger (G:=G) S ∧ 2*extent S.patch < c.val

def Core (V : Config G c) (v : Dir G f) (t : ℝ) := ∀ e : Bond f, collect G v e ≠ 0 → Weak S.patch (S.ratio.parent e.1) V t

theorem revenue (G : Gauge) (P : Patch) (K : KernelChoices) : ∃ C D δ : ℝ, 0<C ∧ 0<D ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G → ∀ F : Forest S.ratio,
    ∀ (V : Config G c) (k : S.Choices) (t : ℝ), 0≤t → t ≤ δ → ∀ v : Dir G f,
      (∀ e∈F.trunks,collect G v e=0) → Core (S:=S) V v t → ∀ e : Bond f,
      let U := replica S.ratio V; let Q := S.ratio.parent e.1
      ‖collect G v e‖ ≤ C* (∑ x∈box (macroR P),∑ a : PlaqAxes,curlPrice U v (wrap f x + S.ratio.embed Q,plaquette a)) +
        (noisePrice U v k (Q,coord e.2) + D*t*coins (S:=S) Q v) := by
  obtain ⟨r,L,hr,hL,hl⟩ := Ball.allows G P K
  obtain ⟨C,hC,hE⟩ := E02.answer G P.L P.J K
  obtain ⟨D,δ,hD,hδ,h⟩ := patchGauge P G
  let m := ((box (macroR P)).card : ℝ)*(Fintype.card PlaqAxes : ℝ)
  let u := C*m*L*D+(L/G.colorScale)*D
  have hs := G.colorScale_pos; have hu : 0<u := by unfold u m; positivity
  refine ⟨C,u,min δ ((r/2)/D),hC,hu, lt_min hδ (div_pos (half_pos hr) hD), fun {c f} S hp hk hS F V k t ht hT v hF he e=>?_⟩
  intro U Q
  let price := curlPrice U v; let sum := ∑ y∈box (macroR P),∑ a : PlaqAxes,price (wrap _ y+S.ratio.embed Q,plaquette a)
  have hnoise : 0≤noisePrice U v k (Q,coord e.2) := div_nonneg (norm_nonneg _) hs.le
  have hc : 0 ≤ coins (S:=S) Q v := Real.sqrt_nonneg _
  by_cases H : collect G v e=0
  · rw [H,norm_zero]; have hy : 0≤sum := Finset.sum_nonneg fun _ _=> Finset.sum_nonneg fun i _=> norm_nonneg _
    exact add_nonneg (mul_nonneg hC.le hy) (by positivity)
  obtain ⟨g,z,hz,hg⟩ := h S hp (hp ▸ hS.2) ht (hT.trans (min_le_left ..)) Q V (hp ▸ he e H)
  have hz' : ‖z‖ < r := by linarith only [hz,(le_div_iff₀ hD).mp (hT.trans (min_le_right ..)),hr]
  let w := field (S:=S) Q g v
  have hw (e₁ : Bond f) : collect G w e₁ = if separation Q (S.ratio.parent e₁.1)≤reach S.patch then G.adjoint (g e₁.1) (collect G v e₁) else 0 := rfl
  have H := F01.link_bound S hS.1.1 F k w (fun e he=> by simp [hw,hF e he]) C hC.le e (fun W hw hW=> hE c f S hk (by rw [hp]) (by rw [hp]) hS.1.2.1 hS.1.2.2 F W hw 1 e k hW)
  rw [hw e, if_pos (by simp [Q]), G.norm_adjoint] at H
  have hEq y (hy : y∈box (macroR P)) (a : PlaqAxes) :
      ‖dColor G f 1 w (wrap _ y+S.ratio.embed Q,plaquette a)‖ ≤ price (wrap _ y+S.ratio.embed Q,plaquette a)+L*D*t*coins (S:=S) Q v := by
    have he' := E08.separation_box_add (S.ratio.embed Q) hy
    have hv := (E04.parent_separation S.ratio _ _).trans (Nat.add_le_add_right he' 1); rw [S.ratio.embed_parent] at hv
    refine (face_price (S:=S) g hz' (by rw [hp]; exact hg) (hl S hp hk) (wrap _ y+S.ratio.embed Q,a) ?_).trans ?_
    · rw [reach,hp]; dsimp only; omega
    unfold price U; rw [mul_assoc L D t]; gcongr
  have hw := wire_price (v:=v) g hz' (by rw [hp]; exact hg) (hl S hp hk) k hS.1.1 (Q,e.2) rfl
  rw [hp] at H
  apply H.trans; apply (add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y hy=> Finset.sum_le_sum fun a _=>hEq y hy a) hC.le) hw).trans
  simp_rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (by positivity : 0≤L/G.colorScale)) hc
  unfold price U u m at *; linarith only [hh]

/-- Actual superposition on the same non-tree chart (any further links
may be exactly zero, no assumption that truncating D commutes with
compression). The upper error/tail fields not involved in this estimate.
Use `Paid` for size/branch requirements, not arbitrary tiny periods. -/
theorem sector_gap (G : Gauge) (P : Patch) (K : KernelChoices) : ∃ η δ : ℝ, 0<η ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G → ∀ F : Forest S.ratio,
    ∀ (V : Config G c) (k : S.Choices) (t : ℝ), 0≤t → t≤δ → ∀ v : Dir G f,
      (∀ e∈F.trunks,collect G v e=0) → Core (S:=S) V v t → let U := replica S.ratio V
      η * (∑ e, ‖v e‖^2) ≤ (∑ p, (curlPrice U v p)^2) + ∑ p, (noisePrice U v k p)^2 := by
  obtain ⟨C,D,r,hC,hD,hr,H⟩ := revenue G P K
  let β := F01.curlFactor P.L (box (macroR P)) C
  let γ := F01.probeFactor P.L
  let size := (((reach P+reach P+1:ℕ):ℝ)^4)
  let price := γ*2*D^2*((Fintype.card (TypeFace 1):ℝ)*size)
  let δ := min 1 (min r ((1/2)/(1+price)))
  let cost := 1+β+γ*2
  have hβ : 0≤β := by unfold β F01.curlFactor; positivity
  have hγ : 0≤γ := by unfold γ F01.probeFactor; positivity
  have hp : 0≤price := by unfold price size; positivity
  have hc : 0<cost := by unfold cost; linarith only [hβ,hγ]
  refine ⟨(1/2)/cost,δ,by positivity,lt_min (by norm_num) (lt_min hr (by positivity)),fun {c f} S hP hk hS F V k t ht hT v hf hv=>?_⟩
  intro U
  let normV := ∑ e,‖v e‖^2
  have ht1 : t≤1 := hT.trans (min_le_left ..)
  have htd := hT.trans ((min_le_right ..).trans (min_le_right r _))
  have hpt : price*t^2 ≤ 1/2 := by
    have h := (le_div_iff₀ (by positivity)).mp htd
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_of_le_one_right ht ht1) hp]
  let E i := coins (S:=S) i v
  let a := curlPrice U v; let b := noisePrice U v k
  let normA := ∑ i,(a i)^2; let normB := ∑ i,(b i)^2
  have hh : ∑ i : Body 1 c,(E i.1)^2 ≤ ((Fintype.card (TypeFace 1):ℝ)*size)*normV := by
    have h := coins_paid S v; rw [hP] at h
    rw [Fintype.sum_prod_type]; simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,← Finset.mul_sum,mul_assoc]; gcongr
  have hB : ∑ i : Body 1 c,(b i+D*t*E i.1)^2 ≤ 2*normB+2*(D*t)^2 * ((Fintype.card (TypeFace 1):ℝ)*size)*normV := calc
    _ ≤ ∑ i : Body 1 c,(2*b i^2 + (2*(D*t)^2)*E i.1^2) := Finset.sum_le_sum fun i _=> by nlinarith only [sq_nonneg (b i-D*t*E i.1)]
    _ ≤ _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum, ← Finset.mul_sum,mul_assoc (2*(D*t)^2)]; gcongr
  have H := F01.sum_estimate S.ratio (box (macroR P)) a (fun i => b i+D*t*E i.1) (fun e=> ‖collect G v e‖) C (fun _=> norm_nonneg _)
      (H S hP hk hS F V k t ht (hT.trans ((min_le_right ..).trans (min_le_left ..))) v hf hv)
  rw [show S.ratio.count=P.L by change S.patch.L=P.L; rw [hP]] at H
  have hv : normV≤β*normA + γ* (∑ i : Body 1 c,(b i+D*t*E i.1)^2) := ((SectorNext.Vacuum.FlatTree.wheel f).sum_comp (fun i=>‖v i‖^2)).symm.trans_le H
  have hfuel := (hv.trans (add_le_add_right (mul_le_mul_of_nonneg_left hB hγ) _))
  have hs : 0≤normV := by unfold normV; positivity
  have ha : 0≤normA := by unfold normA; positivity
  have hb : 0≤normB := by unfold normB; positivity
  have H : (1/2:ℝ)*normV ≤ cost*(normA+normB) := by
    unfold price at hpt; unfold cost
    nlinarith only [mul_le_mul_of_nonneg_right hpt hs,hfuel,hβ,hγ,ha,hb]
  rw [div_mul_eq_mul_div,div_le_iff₀ hc]; linarith only [H]
end YM.Further.CurvedGaussianJets.Pockets
