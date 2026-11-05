import YM.Further.CURVED_GAUSSIAN_JETS.Centers
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Bingo
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Card
/-! # Establish gross n-th derivative of log comparison with normalizers.
 Tilt cap b e estimates . -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Token
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare 
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (A : ChartRatio G)
    (B : BudgetPoint) (ρ : Bid.Dir G c→AxisChart G F) (β : ℝ) (k : S.Choices) {r C U D Z u a s c' : ℝ} {j n : ℕ}
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun (x: Xs)=> represent (tint G _ x))
local notation "R₀" => Pane.virgin T B β
local notation "μ" => Lapis.orbit F ρ
local notation "f₁" => Lapis.table F k T.up T.high
local notation "ψ" => mist F A T.up
local notation "K" => Lapis.gram F T.up T.high ρ k
local notation "φ" => coverLog F T A k ρ β
local notation "G₀" => gStep β
local notation "Ω" => solar F A β
variable (he : LocalRatio A)
    (h : Golf (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) n D U U C)
    {x: Positions (Uniform.Primary c G)}
def pigment (p:ℝ) := cleanLog f₁ ψ μ K p ∘ arc G₀
def lack (p:ℝ) x:= pures T B β x- Real.log Ω + φ x - pigment F T A ρ β k p x
def oat (j:ℕ) (C β : ℝ) := let t : ℝ := clump j (1+C+ (1+C)) C; β*t+t+C
include h
lemma promise (hj : j≤n) (hx: ‖x‖<U) (he:0<β): Brush j (oat j C β) 1 (fun x=>φ x-Lantern.shade (K) 0) x:= by
  let f y:=(y,μ y)
  have hh:= h.curve x hx
  have hC:0≤C:=hh.nonneg
  let I:= ContinuousLinearMap.id ℝ Xs
  have hp: Brush j (1+ C) 1 I x := by
    refine ((Brush.linearB I (u:=1) ?_ ?_ zero_le_one).climb (le_add_of_nonneg_right hC) le_rfl)
    · exact hx.le.trans h.small
    simp [I,ContinuousLinearMap.norm_id_le]
  have hv : Brush j (1+C+(1+C)) 1 f x:= hp.pair ((hh.smaller (by omega)).climb (le_add_of_nonneg_left zero_le_one) le_rfl)
  obtain ⟨h₁,h₂⟩:= h.color 0 0 (0,x) (show ‖(0:Poll.Body (Precision.Key F G))‖≤D by rw [norm_zero]; exact h.off) (by simp) (show ‖(0:ℝ)‖<U by rw [norm_zero]; exact h.pos) hx
  rw [show Lantern.visit μ 0 0 (0,x)=f x from (by simp [Lantern.visit,f])] at h₁ h₂
  have ht := (composite hv (h₁.smaller (by omega))).smul β; rw [Real.norm_of_nonneg he.le] at ht; exact ((ht.gathering (composite hv (h₂.smaller hj))).gathering ((h.gram x hx).2.smaller hj)).shimmy (Eventually.of_forall fun i=> by unfold coverLog; simp [sub_eq_add_neg,f]; abel)

omit h in
lemma octane (hj : j≤n) (hx: ‖x‖<U) (hh : Golf f₁ ψ μ K n D U U C) (he:0<β): Brush j (oat j C β+oat j C β) 1 (fun y=>φ y-φ x) x:= by
  have ht:= promise F T A ρ β k hh hj hx he; let f x:=φ x-Lantern.shade (K) 0
  exact (ht.separating ((Brush.certified zero_le_one _).climb ht.bound le_rfl)).shimmy (Eventually.of_forall fun _=> by simp)
section center
omit h
lemma twist {z a c v d p : ℝ} (hp : 0<p) (he : 0<a) (hv : a ≤ v) (ht : p=Real.exp (d-c)) (hl : z-p*v ∈ Set.Icc 0 (p*u)) :
    0< z ∧ |z|=z ∧ |Real.log z - d + c - Real.log v| ≤ u/a := by
  obtain ⟨hs,hg⟩:=hl; have hv' : 0<v := he.trans_le hv; have hz:0<z:=by linarith [mul_pos hp hv']
  let j:=z/(p*v); have h:1≤j:= by unfold j; rw [le_div_iff₀ (by positivity : 0<p*v)]; linarith
  have hK : Real.log z-d+c-Real.log v=Real.log j := by unfold j; rw [Real.log_div hz.ne' (mul_ne_zero hp.ne' hv'.ne'),Real.log_mul hp.ne' hv'.ne',ht,Real.log_exp]; ring
  refine ⟨hz,abs_of_pos hz,?_⟩; rw [hK,abs_of_nonneg (Real.log_nonneg h)]
  apply (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le h)).trans; unfold j; rw [div_sub_one (by positivity : p*v≠0)]; refine (div_le_div_of_nonneg_left hs (mul_pos hp he) (mul_le_mul_of_nonneg_left hv hp.le)).trans ?_
  have hh : (p*u)/(p*a)=u/a:= by field_simp
  exact (div_le_div_of_nonneg_right hg (mul_nonneg hp.le he.le)).trans_eq hh
lemma gradeAt {x:Xs} (hβ:0<β) (ha:0<a) (H : S.push β (R₀).eval (V x)-(solar F A β* Real.exp (-φ x))*ratify f₁ ψ μ K D (G₀,x)∈ Set.Icc 0 ((solar F A β* Real.exp (-φ x))*u))
    (ht : a≤ratify f₁ ψ μ K D (G₀,x)) (he:LocalRatio A):
    0<tramp T B β x ∧ |lack F T A B ρ β k D x| ≤ u/a := by
  have hp := sun F A β hβ he; obtain ⟨hz,-,hv⟩ := twist (mul_pos hp (Real.exp_pos _)) ha ht (p:=solar F A β* Real.exp (-φ x))
    (c:=φ x) (d:=Real.log (solar F A β)) (by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hp]) H; exact ⟨hz,hv⟩
end center
variable {P : Teller G} (p : Intake P T s (Pane.virgin T B β))
include p
-- Use for getting derivative on the approximation radius; don't need flag
lemma usurp (hj : j≤n) (hx: ‖x‖<U) (hβ:0<β) (hv : Brush j u 1 (pigment F T A ρ β k D) x)
    (ht : 0<tramp T B β x) (hL : (Fintype.card (Bond c):ℝ)≤r) {C' ζ M : ℝ}
    (hQ : PaintSupply G j Z) (hh : 0 ≤ prime G S.kernel j Z C' β r) (he' : Brush j C' 1 Real.exp 0)
    (hk : Brush j ζ 1 Real.log 1) (hw : |lack F T A B ρ β k D x|≤ M) :
      Brush j (clump j (prime G S.kernel j Z C' β r) ζ +(oat j C β+oat j C β)+(u+u)+M) 1 (lack F T A B ρ β k D) x := by
  have hu := thrush F T B β p hQ hL x (hx.trans_le h.small) he' hh hk ht
  have hp := hv.separating ((Brush.certified zero_le_one _).climb hv.bound le_rfl)
  refine (((hu.gathering (octane F T A ρ β k hj hx h hβ)).separating hp).gathering ((Brush.certified zero_le_one _).climb hw le_rfl)).shimmy ?_; refine Eventually.of_forall fun y=>?_; unfold lack; ring_nf
end YM.PhysicalNext.Repeat.Token
