import YM.Further.CURVED_GAUSSIAN_JETS.Cut
import YM.Further.CURVED_GAUSSIAN_JETS.Prices
import YM.Next.FLUCTUATIONS.Locality
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.GridCost
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
import YM.SectorNext.VACUUM_NORMALIZATION.Scheme


/-!
# In each active neighborhood: lower-gap tests transferred from a local gauge

Take at actual periodic `represent`-relative inputs, arbitrary *same-tag*
predictor. `Weak` only on a per-anchor requirement locally on coarse
chords; no global gauge closeness (even on a nonwrapping torus with
holonomies). Enough by E08 axial and `extend_interior`; freeze the gauge
for derivatives. `coins` account for redistribution of errors in real
counting norm; do not price them by a period-dependent sup/l² assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Pockets
open SectorNext.Vacuum Function Filter Set Metric Gauge Lattice Wilson RG Precision Work Exterior Pressure Bid Next.Fluctuations Push.Uniform
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {G : Gauge} {c f n : Side} (S : StepData c f) (P : Patch)

def reach := macroR P+5+predReach P
def extent := reach P+1

def Weak (x : Site c) (V : Config G c) (t : ℝ) : Prop := ∀ b : Cell c,separation x b.1 ≤ extent P → toll V b ≤ t
lemma patchGauge (G : Gauge) : ∃ C δ : ℝ, 0<C ∧ 0<δ ∧ ∀ {c f : Side} (S : StepData c f), S.patch=P →
    2*extent P<c.val → ∀ {t : ℝ}, 0≤t → t ≤ δ → ∀ (x : Site c) (V : Config G c), Weak P x V t →
      ∃ (k : Site f → G.El) (z : Dir G f), ‖z‖ ≤ C*t ∧ AgreeNear S.ratio.parent x (reach P)
        (Lattice.gauge k (replica S.ratio V)) (represent z) := by
  obtain ⟨D,δ,hD,hδ,H⟩ := extend_interior G
  let E := 16*(2*(extent P:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)
  have hE : 0≤E := by unfold E; positivity
  refine ⟨1+D*E,δ/(1+E),by positivity,by positivity,fun S hp hS t ht hT x V hx=>?_⟩
  obtain ⟨k,hk⟩ := E08.axial_patch x V (reach P) (extent P) le_rfl hS t ht fun i hi p=> hx (i,p) hi
  have he : E*t≤δ := by have hh := (le_div_iff₀ (by positivity)).mp hT; linarith only [hh,ht]
  obtain ⟨z,hz,H⟩ := H S.ratio.parent x (reach P) (gauge (constantGauge k S.ratio) (replica S.ratio V)) (E*t) (by positivity) he
      (fun e h=> by rw [copied _ S.patch.odd_side,replica]; split; rw [G.chord_one]; positivity; exact hk _ h)
  exact ⟨_,z,hz.trans (by nlinarith),H⟩

variable {S}
def wake (x : Site c) (v : Dir G f) := ∑ i, if separation x (S.ratio.parent (i : Body 1 f).1) ≤ reach S.patch then ‖v i‖^2 else (0:ℝ)
def coins (x : Site c) (v : Dir G f) := Real.sqrt (wake (S:=S) x v)
def field (x : Site c) (h : Site f → G.El) (v : Dir G f) : Dir G f := fun i =>
    if separation x (S.ratio.parent i.1) ≤ reach S.patch then G.adjoint (h i.1) (v i) else 0
variable (S) in
lemma wake_nonneg (x : Site c) (v : Dir G f) : 0≤wake (S:=S) x v := by unfold wake; positivity
variable (S) in
lemma coins_paid (v : Dir G f) : ∑ x : Site c,coins (S:=S) x v ^2 ≤ (((reach S.patch+reach S.patch+1:ℕ):ℝ)^4)* (∑ i,‖v i‖^2) := by
  simp_rw [coins,Real.sq_sqrt (wake_nonneg ..),wake]; rw [Finset.sum_comm,Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have he : Finset.univ.filter (fun x=> separation x (S.ratio.parent i.1)≤reach S.patch) ⊆ halo (reach S.patch) {S.ratio.parent i.1} := fun x hx=> halo_spec.mpr
      ⟨_,Finset.mem_singleton_self _,separation_comm x _ ▸ (Finset.mem_filter.mp hx).2⟩
  have h := (Finset.card_le_card he).trans (Corona.halo_size ..); rw [Finset.card_singleton,one_mul] at h; exact_mod_cast h
variable (S) in
lemma field_norm (x : Site c) (h : Site f → G.El) (v : Dir G f) : ‖field (S:=S) x h v‖ ≤ coins (S:=S) x v := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  unfold field; split <;> rename_i he
  · rw [G.norm_adjoint]; apply Real.le_sqrt_of_sq_le
    convert! Finset.single_le_sum (s:=Finset.univ) (f:=fun i : Body 1 f => if separation x (S.ratio.parent i.1) ≤ reach S.patch then ‖v i‖^2 else 0) (fun i _=> by positivity) (Finset.mem_univ i) using 1
    rw [if_pos he]
  rw [norm_zero]; exact Real.sqrt_nonneg _

def step (U : Config G f) (v : Dir G f) (t : ℝ) := increment U (t • collect G v)
def curlPrice (U : Config G f) (v : Dir G f) (b : Body 2 f) := ‖deriv (fun t : ℝ => G.curvature (faceValue (step U v t) ((Cut.turn f).symm b))) 0‖
def noisePrice (U : Config G f) (v : Dir G f) (k : S.Choices) (b : Body 1 c) := ‖deriv (fun t : ℝ=> G.mat (S.prediction (step U v t) k ((FlatTree.wheel c).symm b))) 0‖/G.colorScale
lemma steps {U : Config G f} {x : Site c} {h : Site f → G.El} {z : Dir G f}
    (hz : AgreeNear S.ratio.parent x (reach S.patch) (gauge h U) (represent z)) (v : Dir G f) (t : ℝ) :
    AgreeNear S.ratio.parent x (reach S.patch) (gauge h (step U v t)) (Ball.build (t • field (S:=S) x h v,z)) := by
  intro e he
  simp only [Ball.build,Pockets.step, Lattice.gauge,increment, Pi.smul_apply,collect]
  rw [field,if_pos (show separation x (S.ratio.parent e.1) ≤ reach S.patch from he),←map_smul, ProjectorNext.Equivariance.exp_adjoint, ← hz _ he, Lattice.gauge]; group
lemma predicted (hh : S.patch.Branches S.kernel G) (h : Site f → G.El) (U : Config G f) (k : S.Choices) :
    S.prediction (Lattice.gauge h U) k = gauge (h ∘ S.ratio.embed) (S.prediction U k) := by
  funext i; unfold StepData.prediction; rw [S.updateGauged hh, (S.patch.bond_gauge (h:=hh) ..).2]; rfl

variable {U : Config G f} {v z : Dir G f} {x : Site c} {r C : ℝ} (h : Site f → G.El)
    (hz : ‖z‖ < r) (he : AgreeNear S.ratio.parent x (reach S.patch) (gauge h U) (represent z))
    (hs : ∀ z : Ball.Pair G f, ‖z‖ < r → (∀ p, Allows 2 (Ball.direct p) z C) ∧ (∀ k p, Allows 2 (Ball.noise S k p) z C))
include hz he hs
lemma face_price (b : Cell f) (hb : separation x (S.ratio.parent b.1)+4≤reach S.patch) :
    let w := field (S:=S) x h v
    ‖F03.faceCurl b w‖ ≤ curlPrice U v (b.1,plaquette b.2)+ C*‖z‖*coins (S:=S) x v := by
  intro w
  have hc z hz := (hs z hz).1 b
  have hf := Ball.fares hc z w hz (Ball.zero_direct b w)
  let g := fun t : ℝ => Ball.direct b (t • w,z)
  let g₁ := fun t : ℝ => G.curvature (faceValue (step U v t) b)
  have ht (t) : g₁ t = G.adjoint ((h b.1)⁻¹) (g t) := by
    unfold g Ball.direct
    rw [←(show faceValue (Lattice.gauge h (step U v t)) b = faceValue (Ball.build (t • w,z)) b from
      travel_near _ (E03.parent_step S) _ _ b.1 (square ..) 4 le_rfl ((steps he v t).shrink hb)), face_gauge, G.curvature_conjugate, ← G.adjoint_mul]; simp [g₁]
  have hg := Ball.chart_diff hc z w hz
  have hx := (G.adjoint ((h b.1)⁻¹)).toContinuousLinearMap.hasFDerivAt (x:=g 0) |>.comp_hasDerivAt (0:ℝ) hg
  change HasDerivAt (fun t : ℝ => G.adjoint ((h b.1)⁻¹) (g t)) _ 0 at hx
  have hV := hx.deriv; simp_rw [← ht] at hV
  have hy : curlPrice U v (b.1,plaquette b.2) = ‖deriv g 0‖ := by
    unfold curlPrice; rw [show (Cut.turn ..).symm (b.1,plaquette b.2) = _ from (Cut.turn f).symm_apply_apply b]
    rw [hV, hg.deriv]; exact G.norm_adjoint _ _
  rw [hy]; exact hf.trans (add_le_add_right (mul_le_mul_of_nonneg_left (field_norm S x h v) (mul_nonneg (hc (0,z) (by simpa [Prod.norm_def])).nonneg (norm_nonneg _))) _)

lemma wire_price (k : S.Choices) (hh : S.patch.Branches S.kernel G) (b : Bond c) (hb : b.1=x) :
    let w := field (S:=S) x h v
    ‖bills S w (b.1,coord b.2)‖ ≤ noisePrice U v k (b.1,coord b.2)+ (C/G.colorScale)*‖z‖*coins (S:=S) x v := by
  subst x; intro w
  let g := fun t : ℝ => Ball.noise S k b (t • w,z); let r := S.ratio.embed
  let i := r b.1; let j := r (b.1+Lattice.step b.2)
  have ht t : S.prediction (step U v t) k b = (h i)⁻¹ * S.prediction (Ball.build (t • w,z)) k b * h j := by
    have he := prediction_near_eq hh _ _ k b ((steps he v t).shrink (by simp [reach]))
    rw [← he,predicted hh]
    change _ = (h i)⁻¹ * (h i * _ * (h j)⁻¹) * h j; group
  have hc z hz := (hs z hz).2 k b
  have hf := Ball.fares hc z w hz (Ball.zero_noise S hh k b w)
  have hg : HasDerivAt g _ 0 := Ball.chart_diff hc z w hz
  have hr : 0<G.colorScale := G.colorScale_pos
  rw [G.colorMat_norm] at hf
  unfold noisePrice; rw [show (FlatTree.wheel c).symm (b.1,coord b.2)=b from (FlatTree.wheel c).symm_apply_apply b]
  simp_rw [ht,G.mat_mul]; change _ ≤ ‖deriv (fun t : ℝ => G.mat ((h i)⁻¹)*g t*G.mat (h j)) 0‖ /_ + _
  rw [show deriv (fun t : ℝ => G.mat ((h i)⁻¹)*g t*G.mat (h j)) 0 = _ from ((hg.const_mul (G.mat ((h i)⁻¹))).mul_const (G.mat (h j))).deriv, ← hg.deriv,frob_mul_eq _ _ (G.mat_mul_star _),mul_frob_eq _ _ (G.mat_star_mul _)]
  apply le_of_mul_le_mul_left (a:=G.colorScale) _ hr
  calc
    _ ≤ _ := hf
    _ ≤ ‖deriv g 0‖ + C*‖z‖*coins (S:=S) b.1 v := by apply add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (field_norm S b.1 h v) (mul_nonneg (hc (0,z) (by simpa [Prod.norm_def])).nonneg (norm_nonneg _)))
    _ = _ := by field_simp; rfl
end YM.Further.CurvedGaussianJets.Pockets
