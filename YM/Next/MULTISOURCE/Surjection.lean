import YM.Next.MULTISOURCE.Ends
import YM.Next.MULTISOURCE.LevelD

/-! uniform but called with HORRIBLY volume-costed bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Step
open RG Wilson Lattice MeasureTheory Function Marker Finset Filter Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {n : Side} {P : Rep G n}

lemma box_charge (P : BudgetPoint) (θ : ℝ) (F : Config G n → ℂ) (b : ℝ) (Y : Support n)
    (hh : ∀ (d : Directions G n) x,P.dirBound x d → ‖d‖≤ θ) (h : SimpleBound P θ b F) :
    Banked P 2 Y (masked P.threshold univ F) (burn P 2 (univ : Support n)*b) := by
  apply Banked.term (Finset.subset_univ _) h.bounded.nonneg
  · constructor
    · intro U V hx; exact congrArg _ (funext fun i => hx i (mem_univ _) (mem_univ _))
    · exact h.hom.measurable
    · exact h.sym
    · intro U hU; exact ((h.bounded.smooth [] (Nat.zero_le _) U).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    intro U hU A l hl; exact h.bounded.smooth.has hl.le U A
  intro i hi; refine ⟨h.bounded.nonneg,fun U hu l hx hX => ?_⟩
  simpa only [one_pow,mul_one] using h.bounded.bound l hx (fun j hj => hh j i (hX j hj)) U trivial

def right (P : Rep G n) (g f : Config G n→ℂ) : Pulse G n := (masked P.p.threshold univ f,
    fun q U => if q.zone=univ ∧ flags P.p.threshold U=q.flagsAt then (Real.exp (-P.exponent U):ℂ)*g U else 0)
lemma right_paid (P : Rep G n) {σ A B δ p : ℝ} (h : P.Lawful σ A B δ p) (hp : GaugeInvariant P.exponent)
    (b m : ℝ) {θ κ : ℝ} (he : ∀ d : Directions G n,∀ x, P.p.dirBound x d → ‖d‖≤θ) (hκ : 0<κ) : ∃ C : ℝ,
      ∀ g f : Config G n→ℂ,SimpleBound P.p θ m f → FitsPurse b g → ∀ X : Support n, X.Nonempty →
      Credit P.p 2 κ X (right P g f) C := by
  obtain ⟨hZ,C,hC⟩ := (P.exponentEnv h).neg.exp
  let u := burn P.p 2 (univ : Support n)
  let w (q : Pack n) := burn P.p 2 q.zone
  let Z := ∑ i,w i*(C*b)
  refine ⟨max (u*m) (Z/κ),fun g f hG hF X hX => ?_⟩
  have hv : 0 ≤ u*m := mul_nonneg (burn_pos ..).le hG.bounded.nonneg
  refine ⟨hX,by norm_num,hκ,hv.trans (le_max_left ..),⟨0,(right P g f).1,(by funext U; rw [zero_add]),fun _ => rfl,
    norm_zero.trans_le (hv.trans (le_max_left ..)), (box_charge P.p θ f m X he hG).enlarge (le_max_left ..)⟩,
    (fun _ => C*b),?_,?_⟩
  · rw [mul_comm κ]; exact (div_le_iff₀ hκ).mp (le_max_right (u*m) (Z/κ))
  have hx : 0 ≤ C*b := mul_nonneg ((norm_nonneg _).trans (hC 1)) hF.nonneg
  intro i
  by_cases h : i.zone=univ
  · refine ⟨⟨?_,?_,?_,?_⟩,fun _ => h ▸ subset_univ X,hx,?_⟩
    · simp only [right,h,true_and]
      apply Measurable.ite (flags_measurable_eq ..) _ measurable_const; exact
        (Complex.continuous_ofReal.measurable.comp hZ).mul hF.borel
    · intro t U; unfold right
      simp only [h,true_and,gauge_flags,hp t U,hF.symmetry t U]
    · intro U V he _; rw [show U=V from funext fun j => he j (h ▸ mem_univ _) (h ▸ mem_univ _)]
    · simp only [right,h,true_and,Finset.univ_inter]; intro U; split <;> simp_all
    simp only [right,h,true_and]; intro U; split
    · rw [norm_mul,Complex.norm_real]; exact mul_le_mul (hC U) (hF.all U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
    rw [norm_zero]; exact hx
  rw [show (right P g f).2 i=0 from funext fun x => by simp [right,h]]
  exact ⟨Legible.zero ..,fun H => False.elim (H rfl),hx,fun _ => norm_zero.le.trans hx⟩

lemma box_true (U : Config G n) (P : Rep G n) : Healthy P.p.threshold univ U ↔ flags P.p.threshold U=∅ := by simp [Healthy,Finset.disjoint_left,Finset.ext_iff]

private lemma clears_all (W : Finset (Pack n)) (X : Support n) (_hx : X.Nonempty) (h : W∈ Pack.clears X) (j : Pack n) (hp : j∈W)
    (hj : j.zone=univ) : W={j} ∧ X=j.flagsAt := by
  obtain ⟨H,hV⟩ := (mem_filter.mp h).2
  have hf : W={j} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hp,fun i hi => ?_⟩
    by_contra hh
    obtain ⟨v,hv⟩ := i.property.1; exact Finset.disjoint_left.mp (H hi hp hh) (i.property.2 hv) (hj ▸ mem_univ v)
  rw [hf,Finset.singleton_biUnion] at hV
  exact ⟨hf,hV.symm⟩

lemma right_valid (P : Rep G n) (g f : Config G n → ℂ) (h : recept P.p g (fun U => (P.eval U:ℂ)*f U)) :
    recept P.p (right P g f).1 f ∧ tangent P (right P g f)=g := by
  refine ⟨fun x hx => masked_eq _ _ _ _ ((box_true x P).mpr hx),?_⟩
  funext U; by_cases ht : (flags P.p.threshold U).Nonempty
  · let X : Pack n := ⟨⟨univ,_⟩,ht, subset_univ _⟩
    have he : {X} ∈ Pack.clears (flags P.p.threshold U) := Finset.mem_filter.mpr ⟨mem_univ _,by simp; rfl⟩
    unfold tangent; rw [show (right P g f).1 U=0 from masked_ne _ _ _ _ (fun h =>
      nonempty_iff_ne_empty.mp ht ((box_true U P).mp h)), mul_zero,zero_add]
    rw [Finset.sum_eq_single {X}]; rotate_left
    · intro b hb H; refine sum_eq_zero fun i hi => ?_
      have hn : i.zone ≠ univ := by
        intro h; apply H
        obtain ⟨hv,hk⟩ := clears_all b _ ht hb i hi h
        rw [hv, show i=X from Subtype.ext (Prod.ext h hk.symm)]
      simp [right,hn]
    · simp [he]
    rw [sum_singleton, erase_singleton,prod_empty,mul_one]
    simp only [right, show X.zone=univ from rfl,show X.flagsAt=flags P.p.threshold U from rfl,true_and,if_true,
      ← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,add_neg_cancel, Real.exp_zero,Complex.ofReal_one,one_mul]
  rw [tangent]
  have he := not_nonempty_iff_eq_empty.mp ht
  rw [h U he]
  simp [right,he,masked_eq _ _ _ _ ((box_true U P).mpr he), fun i : Pack n => (nonempty_iff_ne_empty.mp i.property.1).symm]
end YM.Multi.Step
