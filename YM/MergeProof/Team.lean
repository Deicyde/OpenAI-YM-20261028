import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Postcards

/-!
# Several leaves of the Repeat/Lotus expansion

Absolute step for a polynomial of probes will use finite, possibly many
simultaneous Leaves. Here the exact differentiated coefficients retain the
same addresses on the vacuum dictionary. Rule: use any Wing at most once.
We use real payloads initially (coefficient multiplication by complex marker
polynomials via a later finite sum). Counts/weights will be charged only on
connected components. Proofs in Team* adaptations of Lotus.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented  Sector Footprint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {W a r σ E Λ μ x κ w C : ℝ}

-- If two live leaves on one Wing the product coefficient is not used. For
-- simultaneous log-source inputs allocate distinct blank addresses as needed.
structure Team (R : Rep G f) where
  own : Finset (Leaf R)
  alone : Set.InjOn Leaf.turn (own:Set (Leaf R))

namespace Team
variable (M : Team R)
def signs (S : StepData c f) : Molecule S:= M.own.image fun i=> i.turn.badge S

lemma badged (S : StepData c f): Injective (fun a:Wing=> a.badge S) := by rintro (a|a) (b|b) h <;> simp [Wing.badge] at h <;> simp [h]


def gasDue:= (M.own.image (fun i => match i.turn with | .logKey _ => (Sum.inl () : Unit ⊕ ℕ) | .gasKey i => Sum.inr i)).toRight
def logs:= (M.own.image (fun i=> match i.turn with | .logKey i=> (Sum.inl i:ℕ ⊕ Unit) | .gasKey _=> Sum.inr ())).toLeft
@[simp] lemma asked (i:ℕ) : i∈M.gasDue ↔ ∃ a∈ M.own,a.turn=.gasKey i:=by
  simp only [gasDue,mem_toRight,mem_image]; refine exists_congr fun b=> and_congr_right fun hb=>?_ ; cases b.turn <;> simp
@[simp] lemma sent (i:ℕ) : i∈M.logs ↔ ∃ a∈M.own,a.turn=.logKey i:=by
  simp only [logs,mem_toLeft,mem_image]; refine exists_congr fun b=> and_congr_right fun hb=>?_ ; cases b.turn <;> simp

def weight : ℝ := ∏ i∈M.own,i.weight
lemma profit : 0≤M.weight:=prod_nonneg fun i _=> i.profit
def ingredients (U:Config G f):ℝ:= ∏ i ∈ M.own,i.ingredient U
lemma borel : Measurable M.ingredients:= Finset.measurable_fun_prod _ fun i _=>i.borel
lemma earn (U: Config G f): ‖M.ingredients U‖≤M.weight:=by
  unfold ingredients; rw [norm_prod]; exact prod_le_prod (fun _ _=>norm_nonneg _) fun i _=>i.earn U

def bill (k : Finset ℕ) (U : Config G f):= if M.gasDue ⊆ k then M.ingredients U * ∏ i∈k\M.gasDue,R.activities.K i U else 0

def bun (k : Finset ℕ) (U : Config G f) := if R.activities.admissible R.p U k then M.bill k U else 0

def cicada (U: Config G f):ℝ:=Real.exp (R.exponent U)*(∑' k,M.bun k U)

lemma proud (h: R.Lawful σ C Λ x w) (k : Finset ℕ) : Measurable (M.bun k) := by
  unfold bun; apply Measurable.ite (R.activities.admissible_borel R.p k) _ measurable_const
  unfold bill; by_cases hp : M.gasDue ⊆ k
  · simp_rw [if_pos hp]; exact M.borel.mul (Finset.measurable_fun_prod _ fun i _=> h.labels.forced.meas i)
  simp_rw [if_neg hp]; exact measurable_const

def crowns {i : Type*} [DecidableEq i] (X : i→ℝ) (v : ℝ) (p:Finset i) : Finset i → ℝ:=fun F=> if p⊆F then v*∏ i∈ F\p,X i else 0
lemma crowns_has {i:Type*} [DecidableEq i] {X:i→ℝ} (v : ℝ) (p:Finset i) (he : Summable X) (hp : ∀ i,0≤X i) : Summable (crowns X v p):=by
  have hh : Summable (fun k:{a:Finset i|p⊆a} => crowns X v p k.val) := ?_
  · have hz : Function.support (crowns X v p) ⊆ {a|p⊆a} := fun i hi=> by by_contra ht; exact hi (by simp only [crowns,if_neg (show ¬p⊆i from ht)])
    exact ((hasSum_subtype_iff_of_support_subset hz).mp hh.hasSum).summable
  let A:= fun k:{i:Finset i|p⊆i}=> k.val\p
  have h : Summable (fun i=>∏ j∈ A i,X j) := (summable_finsetProd_of_summable_nonneg hp he).comp_injective
    (fun a b hg=> Subtype.ext (((sdiff_union_of_subset a.property).symm.trans ((congr_arg (· ∪ p) hg).trans (sdiff_union_of_subset b.property)))))
  apply Summable.congr (h.mul_left v); intro s; exact (if_pos s.property).symm
lemma bud (h: R.Lawful σ C Λ x w) : Dominated M.bun := by
  obtain ⟨b,hB,h⟩:= R.activities.K_total h.labels.boundK
  have hb i:= (h i).1
  refine ⟨crowns b M.weight M.gasDue,crowns_has _ _ hB hb,fun k U=>?_⟩
  by_cases he : M.gasDue ⊆ k
  · unfold bun bill crowns; rw [if_pos he, if_pos he]; split
    · rw [norm_mul,norm_prod]; exact mul_le_mul (M.earn _) (prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> (h i).2 _)) (prod_nonneg fun i _=> norm_nonneg _) M.profit
    rw [norm_zero]; exact mul_nonneg M.profit (prod_nonneg fun i _ => hb i)
  have hf : M.bun k U=0:=by simp [bun,bill,he];
  rw [hf,norm_zero,crowns,if_neg he]
lemma sells (h: R.Lawful σ C Λ x w) : Envelope M.cicada ∧ GaugeInvariant M.cicada:=by
  have hb:Envelope (fun U=>∑' k,M.bun k U):= ⟨Measurable.tsum (M.proud h),(M.bud h).bound⟩
  refine ⟨(R.exponentEnv h|>.exp).mul hb,fun t U=>?_⟩; unfold cicada
  rw [Further.DenseMixedKernels.Throng.phase h t U]
  exact congr_arg (Real.exp (R.exponent U)*·) (tsum_congr fun i=> (by simp only [bun,bill,ingredients,Leaf.glows _ t U,h.labels.forced.sym _ t U, Activities.admissible,gauge_flags]))

lemma counted (h : R.Lawful σ C Λ x w) (k : Finset ℕ) (U : Config G f) (ht : Contract.sealed R k) : M.bun k U=Contract.order R k univ U*M.bill k U:=by
  unfold bun; split
  next hp =>
    have hq : Contract.order R k univ U=1:=by
      apply prod_eq_one; intro i _; unfold Contract.charges; apply if_neg
      rintro ⟨h₁,h₂⟩; apply h₁; rw [←hp.2] at h₂; obtain ⟨a,ha,hb⟩:= mem_biUnion.mp h₂; exact mem_biUnion.mpr ⟨a,ha,(R.activities.forced a).inventory_sup hb⟩
    rw [hq,one_mul]
  next hz=>
    by_contra! h'
    have he:=left_ne_zero_of_mul (Ne.symm h'); have hp:=right_ne_zero_of_mul (Ne.symm h')
    unfold bill at hp; split at hp
    swap; · exact hp rfl
    next hκ=>
    have hF (j:ℕ) (hj:j∈k) : (R.activities.forced j).eligible R.p.threshold U:=by
      by_cases hi:j∈M.gasDue
      · obtain ⟨a,ha,ht⟩:= (M.asked _).1 hi
        have he:= a.grant U (fun hh=> left_ne_zero_of_mul hp (prod_eq_zero ha hh))
        rw [ht] at he; exact he
      exact h.labels.forced.permit j U fun hn=> right_ne_zero_of_mul hp (prod_eq_zero (mem_sdiff.mpr ⟨hj,hi⟩) hn)
    refine hz ⟨ht,?_⟩; ext i; constructor
    · intro hi; obtain ⟨v,hv,hj⟩:= mem_biUnion.mp hi; exact (mem_inter.mp ((hF v hv).1.symm ▸ hj : i∈(R.activities.forced v).support∩RG.flags R.p.threshold U)).2
    intro hi
    have hs:i∈ covered R k:= by by_contra hn; exact he (prod_eq_zero (mem_univ _) (show charges R k U i=0 from if_pos ⟨hn,hi⟩))
    obtain ⟨v,hv,hj⟩:=mem_biUnion.mp hs; exact mem_biUnion.mpr ⟨v,hv,(hF v hv).1 ▸ mem_inter.mpr ⟨hj,hi⟩⟩
end Team
end YM.PhysicalNext.Repeat.Lotus
