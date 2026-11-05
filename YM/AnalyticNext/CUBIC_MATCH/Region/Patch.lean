import YM.AnalyticNext.CUBIC_MATCH.Region.TrialCost
import YM.AnalyticNext.CUBIC_MATCH.Region.WalkCost
import YM.AnalyticNext.CUBIC_MATCH.Trial


set_option warningAsError false

/-!
# The S.patch reading

Still arbitrary t. Footprint grows with J, estimates here explicitly scale
with J in the chosen constants; no commitment uniform over all shapes J. `Theta`
positive from a shape/algebra invoice. Integrations etc not purchased. These
costs will pay for two coefficients of the *prediction* (with noncentral
terms in both frame and compensation).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Push Branch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {μ : Type*} {L : Side} {c f : μ → Side}
  {θ C B : ℝ} {V : ∀ p, Dir G (c p) → Dir G (f p)} {P : Patch} {K : KernelChoices}

/-- At fixed shape and all periods indexed. -/
abbrev perform (P : Patch) (K : KernelChoices) (eqs : ∀ p, (f p).val=(c p).val * P.L.val) (p : μ) : StepData (c p) (f p) := ⟨P,K,eqs p⟩

lemma route_span (x y : Cover) (s : Lattice.Order) : (route x y s).length=size (y-x) := by
  unfold route allAxes axisRoute size
  rw [← Equiv.sum_comp s]
  have he : List.finRange 4=[(0:Axis),1,2,3] := by decide
  simp [he,straight,Axis,Fin.sum_univ_succ]
lemma box_size (x : P.Points) : size x.val ≤ 4*P.radius := by
  have hh := box_test.mp x.property
  unfold size; exact (Finset.sum_le_sum (g:=fun _ => P.radius) (fun i _ => by have hx := hh.1 i; have hv := hh.2 i; omega)).trans_eq (by simp [Axis])

def radar (J : ℕ) := 12*(J+3)
lemma radar_reach (x y : P.Points) (s : Lattice.Order) : size x.val+(route x.val y.val s).length ≤ radar P.J * P.L.val := by
  rw [route_span]; have hh := size_add y.val (-x.val); rw [← sub_eq_add_neg,size_neg] at hh
  rw [radar, Nat.mul_assoc,← show P.radius=(P.J+3)*P.L.val from rfl]
  have he := box_size x; have ht := box_size y; omega


/-- Size allowance only J-shaped. -/
def journey (G : Gauge) (J : ℕ) (C θ : ℝ) := (radar J : ℝ)*tileFee G C * Real.exp (θ*radar J)


section payable
variable (eqs : ∀ p, (f p).val=(c p).val * P.L.val)
variable (h : ScaleRead c f P.L (mainRoot eqs) V θ C)

include h

/-- Costs of all mat travels within the route. -/
lemma ScaleRead.journeyMat {y : P.Points} (v : Walk) (hp : size y.val+v.length ≤ radar P.J*P.L.val) : RayReceipt c θ
    (journey G P.J C θ) ((journey G P.J C θ)^2) (walkMat V (mainRoot eqs) y.val v) := by
  have ht := h.along _ _ _ hp
  let B := tileFee G C*tilt P.L*phaseCost P.L θ (radar P.J*P.L.val)
  have hA : 0≤B := mul_nonneg (mul_nonneg (tileFee_nonneg h.fee) tilt_pos.le) (phase_pos ..).le
  have he : ((v.length):ℝ) * B ≤ journey G P.J C θ :=
      (mul_le_mul_of_nonneg_right (show (v.length:ℝ) ≤ ((radar P.J*P.L.val:ℕ):ℝ) by exact_mod_cast (Nat.le_trans (Nat.le_add_left ..) hp)) hA).trans_eq (by unfold B journey tilt; rw [phase_length];  push_cast; field_simp)
  exact ht.raisePrice he (pow_le_pow_left₀ ht.first.cash he 2)

lemma ScaleRead.roadSum (K : KernelChoices) (u v : P.Points) (o : Lattice.Order) : LocalRep c 1 θ
    (G.colorScale⁻¹ * journey G P.J C θ) (fun p x a => Push.fee (perform P K eqs p) x u v o (V p a)) := by
  let w := route u.val v.val o
  let T := walkMat V (mainRoot eqs) u.val w
  have ht := (h.journeyMat eqs w (radar_reach ..)).first
  refine ht.tint.fits fun p x a => ?_
  have hh : term 1 (T p x a)=G.colorMat (Push.fee (perform P K eqs p) x u v o (V p a)) := by
    rw [term_one]; exact (Push.travell (G:=G) w (wrap (f p) u.val+mainRoot eqs p x) (V p a)).deriv
  change G.projectColor (term 1 (T p x a))=_; rw [hh,G.project_colorMat]
lemma ScaleRead.fees (K : KernelChoices) (i : P.Points) : LocalRep c 1 θ
    (G.colorScale⁻¹ * journey G P.J C θ) (fun p x a => Push.tap (perform P K eqs p) x i (V p a)) :=
  (LocalRep.equalWeights (fun z : P.Points => LocalRep.equalWeights fun o => h.roadSum eqs K i z o)).negative
lemma ScaleRead.rootMotion (K : KernelChoices) : LocalRep c 1 θ (2 * G.colorScale⁻¹*journey G P.J C θ)
    (fun p x a => psi (perform P K eqs p) (V p a) (x,vac)) := by
  have ht := h.fees eqs K
  have he := LocalRep.weighed h.rate ht P.weight_nonneg P.weight_sum
  have hr := (ht P.center).minus he
  refine (hr.raisePrice ?_).fits (fun p x a => ?_)
  · exact le_of_eq (by ring)
  let M := perform P K eqs p; let v := V p a
  ext i
  let L := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hh (z : P.Points) : L (Push.tap M x z v)=_ := Push.tap_line M x v z i
  change L (Push.tap M x P.center v - ∑ i,P.weight i • Push.tap M x i v)=(Matrix.mulVec (fixRoot M) (parts G 1 v i)) (x,vac)
  rw [map_sub,map_sum,hh]; simp_rw [map_smul,hh]; simp only [fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted,LinearMap.sub_apply,
    LinearMap.sum_apply,LinearMap.smul_apply]; rfl
end payable
end YM.CubicMatch
