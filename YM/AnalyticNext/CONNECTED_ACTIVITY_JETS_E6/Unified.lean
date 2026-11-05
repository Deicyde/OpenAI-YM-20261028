import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District

/-!
# Restoration before Mayer

All gamma and likelihood masks checked together. Never replace gamma h with
an exterior multiplication before restoring every mandatory comparison. This
file: finite alarms, exponent exceptions. Use R.gasOccupation. Supports
separate exact equality from profile intersections. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (X : Coat T F)

lemma forceds (Z : Stores S) (R : Rep G f) (l : Finset ℕ) (W : ℝ) (u : Directions G f) :
    let d := 300*X.B
    let U := X.input u
    (∏ p : Panic c f, if mandatory Z X.B p then X.rawStorm u W Z R l p else 1) =
      Contract.order R l (vias S Z d) U * tickets Z d U X.k * profiles Z X.χ d X.x W U X.k X.V := by
  intro d U; let P := Z.dome d
  have he : P=univ.filter fun i => ¬Disjoint P {i} := by ext i; simp
  unfold Panic; simp only [Fintype.prod_sum_type]
  unfold Mask.tickets Mask.profiles Contract.order; dsimp only
  let D (p) := X.rawStorm u W Z R l p
  have ht : (∏ x∈P, Tags.siteMass U X.k x) = ∏ x : Site c, (if mandatory Z X.B (.inr (.inr (.inr (.inl x)))) then D (.inr (.inr (.inr (.inl x)))) else 1) := by
    rw [he,prod_filter]; simp [mandatory,districts, disjoint_singleton_right, D,P,U,rawStorm,d]
  have hp : (∏ x∈vias S Z d, Contract.charges R l U x)=∏ x : Site f, (if mandatory Z X.B (.inr (.inr (.inr (.inr x)))) then D (.inr (.inr (.inr (.inr x)))) else 1) := by
    unfold vias; rw [prod_filter]; refine Finset.prod_congr rfl fun i _ => ?_; dsimp only [mandatory,districts,Sum.elim]
    simp [D, disjoint_singleton_right, Inside,d, rawStorm,U]
  have hz := Z.dome (300*X.B)
  rw [hp,ht]; unfold readFine readBonds; simp_rw [prod_filter]; unfold mandatory districts
  unfold P D d U at *
  simp only [Sum.elim]; unfold rawStorm; dsimp only [Sum.elim]; ring_nf

lemma share_all {ι : Type*} [Fintype ι] [DecidableEq ι] (χ : Chi) (Z : Finset ι) (d : ℝ) (f : ι→ℝ) :
    (∏ i : ι, if i∈Z then 1-χ.innerShare d (f i) else χ.innerShare d (f i)) = χ.share Z f d := by
  rw [Finset.prod_ite,Chi.share]; simp only [filter_mem_eq_inter,univ_inter]; congr 1
  rw [show univ.filter (fun x => x∉Z)=Zᶜ from by ext; simp]

lemma distributions (u : Directions G f) (W : ℝ) (k : Finset ℕ) (R : Rep G f) (h : X.manifest) :
    (Fintype.card S.Choices:ℝ)⁻¹ * (∏ p : Panic c f, X.rawStorm u W X.seeds R k p) =
      X.χ.distribute X.seeds X.x W (X.input u) X.k X.V *
        S.likelihood (X.input u) X.k * Contract.order R k univ (X.input u) := by
  unfold Chi.distribute Panic; rw [if_pos h.symm]; simp only [Fintype.prod_sum_type]
  unfold rawStorm; simp only [Sum.elim, Mask.fine,Mask.noise]; rw [share_all,share_all, Tags.likelihood_all]
  unfold Chi.fineShare Chi.bondShare Contract.order Coat.t; ring_nf

def tier := univ.filter X.Hot

lemma fuse (u : Directions G f) (a : ℝ) : (X.enforce a u (X.plaza (X.seeds.dome (304*X.B)))) *
    (∏ i : Bond f, (1+ X.aura u a i)) = X.enforce a u X.tier := by
  let Z:= X.plaza (X.seeds.dome (304*X.B)); let P:=X.enforce a u
  have hf : Z ⊆ X.tier := fun i hi => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2.1⟩
  have hh : (∏ i : Bond f,(1+X.aura u a i)) = X.enforce a u (X.tier\Z) := by
    unfold enforce
    rw [show X.tier \ Z = univ.filter (fun i : Bond f=> X.Hot i ∧ i∉Z) by ext; simp [tier],prod_filter]; refine Finset.prod_congr rfl fun i _ => ?_
    by_cases he : X.Hot i ∧ i∉ Z
    · unfold aura; rw [if_pos he,if_pos he]; ring_nf
    unfold aura; rw [if_neg he,if_neg he,add_zero]
  rw [hh,mul_comm]; exact Finset.prod_sdiff hf

lemma underfoot {v : Directions G f} {a : ℝ} (h : 0<a*X.t) (ht : X.enforce a v X.tier≠0) (b : Support c) :
    X.enforce (2*a) v (X.plaza b)=1 := X.covering h _ _ fun i hi hz => ht (prod_eq_zero (show i∈X.tier from
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.1⟩) hz)

lemma precip (R : Rep G f) (Ñ : ChartRatio G) (u : Directions G f) (W a : ℝ) (k : Finset ℕ) (h : X.manifest)
    (he : 0<a*X.t) :
    let G' := Fintype.card S.Choices
    let U:=X.input u
    (G':ℝ)⁻¹ * (X.steam R Ñ k W a X.seeds u * (∏ p : WarningAt c f, (1+X.detect u W a R k p))) =
      Real.exp (X.steamLog R Ñ a X.seeds u)*(X.χ.distribute X.seeds X.x W U X.k X.V * S.likelihood U X.k * Contract.order R k univ U)*X.enforce a u X.tier := by
  intro G' U
  let ZType := Panic c f
  unfold WarningAt detect; rw [Fintype.prod_sum_type]
  unfold steam; simp only [Sum.elim];
  let K : ℝ := (G':ℝ)⁻¹
  let E := Real.exp (X.steamLog R Ñ a X.seeds u)
  let F := X.rawStorm u W X.seeds R k
  let Z : ℝ := ∏ p : Panic c f,(if mandatory X.seeds X.B p then F p else 1)
  let H : ℝ := ∏ p : Panic c f, (1+X.mayor u W a R k p)
  let C := X.enforce a u X.tier
  let A := Contract.order R k (vias S X.seeds (300*X.B)) U
  let Y := tickets X.seeds (300*X.B) U X.k
  let D := profiles X.seeds X.χ (300*X.B) X.x W U X.k X.V
  let V := X.enforce a u (X.plaza (X.seeds.dome (304*X.B)))
  have hh : A*Y*D=Z := (X.forceds ..).symm
  have hg : (K * (E*A*Y*D * V * (H* (∏ i : Bond f, (1+ X.aura u a i)))))= K*E*(Z*H)*C := by
    unfold C; rw [← hh,← X.fuse]; unfold V; ring_nf
  rw [hg]
  by_cases hx : C=0
  · change _ = _*C; rw [hx,mul_zero,mul_zero]
  have hp i : (if mandatory X.seeds X.B i then F i else 1) * (1+X.mayor u W a R k i)= F i := by
    unfold mayor; split
    · simp
    rw [X.underfoot he hx]; unfold F; ring_nf
  have hz : Z*H = ∏ p : Panic c f,F p := by unfold Z H; rw [← prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => hp i
  rw [hz,mul_comm K E,mul_assoc E,show K*(∏ p,F p)=_ from distributions X u W k R h]
end YM.ConnectedActivityE6.Coat
