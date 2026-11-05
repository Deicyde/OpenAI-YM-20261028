import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Many

/-!
# Sharing z coordinates at trigger addresses

t scaling finite with full h. For overlapping molecule keep all
indices at their actual visits. Count copies allowed per same Horn,
including for sites after projecting and reorientation. The payment
can be Rate any r (later absorbed). Doesn't assume μ scales with p⁰.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Poll
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask 
open ProbabilityTheory
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ENNReal Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {M V : ℝ}

section crowd
variable [Fintype κ] (o : κ→Site c) (g : ι→Site c) (t : ℝ) {m p : ℕ}

def Crash (X : Finset κ) (D : ℕ) :=
    {z : Body ι | ∀ i∈X, ∃ j, separation (o i) (g j)≤D ∧ t ≤ |z j|}

omit [DecidableEq ι] [Fintype κ] in
lemma sounded (X : Finset κ) (D : ℕ) : MeasurableSet (Crash o g t X D) := by
  -- finite all. Measurable
  simp only [Crash, Set.setOf_forall, Set.setOf_exists]; apply X.measurableSet_biInter
  intro i _; apply MeasurableSet.iUnion; intro j; by_cases he : separation (o i) (g j)≤D
  · simp only [he, true_and]
    exact measurableSet_le measurable_const (show Continuous (fun z : Body ι => |z j|) by fun_prop).measurable
  simp [he]

lemma count_for (_hg : Census p g) (ho : Census m o) (X : Finset κ) (D : ℕ)
    (F : (k : X) → ↥(withinH g (o k.val) D)) :
    let V := Finset.univ.image (fun i => (F i).val)
    V.card≤X.card ∧ X.card ≤ V.card*(Animals.ballCost D*m) := by
  intro V
  refine ⟨card_image_le.trans_eq (by simp),?_⟩
  let W i := withinH o (g i) D
  apply (le_trans (Finset.card_le_card (show X ⊆ V.biUnion W from ?_)) Finset.card_biUnion_le).trans
    ((Finset.sum_le_sum (g:=fun _=> Animals.ballCost D*m) (fun i _=>Census.count_near ho _ _)).trans_eq (by simp))
  intro i hi; let u : ↥X := ⟨i,hi⟩
  refine mem_biUnion.mpr ⟨(F u).val,mem_image_of_mem _ (mem_univ u), (joins ..).mpr ?_⟩
  exact (separation_comm ..).trans_le ((joins ..).mp (F u).property)

lemma shattered (h : A.PosSemidef) (hv : ∀ v: ι→ℝ, dotProduct v (A *ᵥ v)≤ M*dotProduct v v)
    (hg : Census p g) (ho : Census m o) (X : Finset κ) (D : ℕ) {H : ℝ} (hk : 0≤ H)
    (he : M/2+H*((Animals.ballCost D:ℝ)*m) ≤ t) :
    (sweep A).real (Crash o g t X D) ≤ ((Animals.ballCost D:ℝ)*p*2*Real.exp (-H))^X.card := by
  let U (F : (k:X)→ ↥(withinH g (o k.val) D)) := Finset.univ.image (fun i => (F i).val)
  let N := ((k : X) → ↥(withinH g (o k.val) D))
  let R (F:N) := {z : Body ι | ∀ i∈U F,t ≤ |z i|}
  letI : Fintype N := by unfold N; infer_instance
  let L := (Finset.univ : Finset N)
  apply ((MeasureTheory.measureReal_mono (show Crash o g t X D ⊆ ⋃ i∈L,R i from ?_) (measure_ne_top _ _)).trans
    (measureReal_biUnion_finset_le ..)).trans
  rotate_left
  · intro z hz
    have hp (i:X) : ∃ k : ↥(withinH g (o i.val) D), t ≤ |z k.val| := by
      obtain ⟨k,hh,hk⟩ := hz i.val i.property
      exact ⟨⟨k,(joins ..).mpr hh⟩,hk⟩
    choose F hF using hp
    refine Set.mem_iUnion.mpr ⟨F,Set.mem_iUnion.mpr ⟨mem_univ _,?_⟩⟩; intro i hi
    obtain ⟨u,-,rfl⟩ := mem_image.mp hi; exact hF u
  let e := (Animals.ballCost D:ℝ)*p
  have hcard : L.card ≤ (Animals.ballCost D*p)^X.card := by
    unfold L; rw [card_univ, show Fintype.card N=∏ k : X,Fintype.card (↥(withinH g (o k.val) D)) from Fintype.card_pi]
    apply le_trans (b:=∏ _ : X, (Animals.ballCost D*p))
    · apply Finset.prod_le_prod'; intro i hi; rw [Fintype.card_coe]; exact Census.count_near hg _ _
    simp
  have hp : ((2:ℝ)^X.card)≥0 := by positivity
  have hu F : (sweep A).real (R F) ≤ (2*Real.exp (-H))^X.card := by
    obtain ⟨hX,hh⟩ := count_for o g hg ho X D F
    refine (rectangle h hv (U F) t 1 zero_le_one).trans ?_
    rw [mul_pow,← Real.exp_nat_mul]; refine mul_le_mul (pow_le_pow_right₀ (by norm_num) hX) (Real.exp_monotone ?_ ) (Real.exp_pos _).le hp
    have hm : (X.card:ℝ) ≤ ((U F).card:ℝ)*((Animals.ballCost D:ℝ)*(m:ℝ)) := by exact_mod_cast hh
    nlinarith only [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α:=ℝ) (U F).card), mul_le_mul_of_nonneg_left hm hk]
  apply (Finset.sum_le_sum (fun i _ => hu i)).trans
  rw [sum_const,nsmul_eq_mul,mul_assoc e 2, mul_pow e]
  exact mul_le_mul_of_nonneg_right (by unfold e; exact_mod_cast hcard) (by positivity)
end crowd
end YM.ConnectedActivityE6.Poll
