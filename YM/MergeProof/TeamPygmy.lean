import YM.MergeProof.TeamParcel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Pygmy

/-! # marked body values per Molecule (all Y).
 Includes compulsory assignments. No allocations resampled.
 Keeps K.TEST before H.routing.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Team
variable (M : Team R) (X : Coat T F) (k:Finset ℕ)
def paidU (a : ℝ)(u : Directions G f):= ∏ i∈M.own, i.paidU X a u
def premium (W a : ℝ) (Ñ : ChartRatio G) (l : Finset ℕ) (m : ℕ) (z : Air f G) (p : Molecule S) :=
    if M.signs S⊆p then M.paidU X a (X.liftA R.beta z)* X.term R Ñ W a l m z (p\M.signs S) else 0

def into (W a : ℝ) (Ñ : ChartRatio G) (l : Finset ℕ) (m : ℕ) (p : Molecule S) (z : F.Slice G×Air f G) :=
    M.premium (X.wrapY z.1) W a Ñ l m z.2 p

lemma coin (a : ℝ)(u : Directions G f): ‖M.paidU X a u‖≤M.weight:= by
  unfold paidU; rw [norm_prod]; exact prod_le_prod (fun i _=> norm_nonneg _) fun i _=>i.coin ..
lemma crystall (hi : Intake P T X.x R) (hg : ShellAccess S G X.x W X.width C) (hÑ: LocalRatio Ñ) (a : ℝ) (m:ℕ) (p:Molecule S) : Measurable (M.into X W a Ñ k m p):=by
  unfold into premium; split_ifs
  · have ht:= (X.airwards (v:=Prod.snd) hg hi.ready measurable_fst).2.2 R.beta measurable_snd
    let u (i:F.Slice G × Air f G) := X.wrapY i.1
    let z (i:F.Slice G × Air f G):= (u i).liftA R.beta i.2
    have hp (M : Leaf R) : Measurable (fun i:F.Slice G × Air f G=> M.paidU (u i) a (z i)) := ((M.borel.comp (X.summon measurable_fst ht : Measurable (fun i:F.Slice G × Air f G=> (u i).input (z i)))).mul ((X.enforce_b (2*a) (X.plaza (Matter.areas R T 0 X.B (M.turn.badge S)))).comp ht))
    exact (Finset.measurable_fun_prod _ fun i _=>hp i).mul (X.body_b hÑ hi hg ..)
  exact measurable_const
-- integration bound
lemma tip (H : Cash W X.x μ L Q o C T R) (hk : X.width=o.K) (ha:X.manifest) (p:Molecule S):
    let f:=M.into X W o.a Q.table k Q.halo p; let D:= (F.order G).prod X.dice
    Envelope f ∧ Integrable f D ∧ (∫ i, ‖f i‖ ∂D) ≤ (if M.signs S⊆p then M.weight * ∏ i∈p \ M.signs S, H.text i else 0):=by
  intro f' D; have hR:= H.laws.intake; have hp:Measurable f':= M.crystall X k hR (hk.symm ▸ H.laws.data.access) Q.table_exists ..
  split
  next ht =>
    let P':= p \ M.signs S; let f i := ‖X.body R Q.table W o.a k Q.halo P' i‖
    have hc (i): ‖f' i‖ ≤ M.weight*f i:=by unfold f' into premium; rw [if_pos ht,norm_mul]; exact mul_le_mul_of_nonneg_right (M.coin (X.wrapY i.1) ..) (norm_nonneg _)
    have he : Envelope f':=⟨hp,M.weight*∏ i∈P',H.fair i,fun ⟨s,p⟩=> (hc (s,p)).trans (mul_le_mul_of_nonneg_left (H.every X rfl hk ha k P' s p) M.profit)⟩
    refine ⟨he,he.integrable D,(integral_mono (he.integrable _).norm (((H.integrated X rfl hk ha k P').norm).const_mul M.weight) hc).trans ?_⟩
    rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (H.statements X rfl hk ha k P') M.profit
  next h =>
    unfold f' into premium; simp_rw [if_neg h]
    exact ⟨Envelope.const _,integrable_const _,by simp⟩
-- umbrella gas series, regular requires dummy E not reserved globally.
def comfortP (a : ℝ) (u : Directions G f):=
    if M.gasDue ⊆ k then M.paidU X a u*∏ i∈ (k \ M.gasDue),X.bag R a u i else 0

def salary (W a : ℝ) (Ñ : ChartRatio G) (Y : Finset (Stores S)) (z : Air f G):=let u:=X.liftA R.beta z
    ((∏ A∈Y,X.Pack R Ñ k W a A u)*M.comfortP X k a u*
      (∏ p : WarningAt c f,(1+X.detect u W a R k p))) * Real.exp (∑' p,X.farLog R a Ñ z p)

lemma approved (D:Cash W X.x μ L Q o C T R) (h : X.manifest) (hk : X.width=o.K) (z : Air f G) {Y : Finset (Stores S)}
    (hp : Layout X.seeds Q.halo X.B Y) (hL : Contract.sealed R k) :
    X.tokenUTeam M W o.a Q.table z k = X.levy R * X.deducted Q.table R.beta *
      ((Fintype.card S.Choices:ℝ)⁻¹*M.salary X k W o.a Q.table Y z)*X.thetaRef z := by
  let F₀:=D.laws.data
  let u := X.liftA R.beta z; let U:= X.input u
  have he : 0<o.a*X.t := mul_pos o.large F₀.room.fiery
  have hx := X.precip R Q.table u W o.a k h he
  let K' : ℝ := (Fintype.card S.Choices:ℝ)⁻¹
  let g := X.enforce o.a u X.tier
  let C₁ := X.χ.distribute X.seeds X.x W U X.k X.V
  let t := X.cross_link z
  let w := Contract.order R k univ U
  let L := S.likelihood U X.k
  let c':= M.comfortP X k o.a u
  have hy : K'*M.salary X k W o.a Q.table Y z=
      Real.exp (X.steamLog R Q.table o.a X.seeds u)*(C₁*L*w)*g*
       c'*Real.exp (∑' p,X.farLog R o.a Q.table z p) := by
    let f' := X.steam R Q.table k W o.a X.seeds u
    let b := ∏ p : WarningAt c f, (1 + X.detect u W o.a R k p)
    rw [show Real.exp (X.steamLog R Q.table o.a X.seeds u)*(C₁*L*w)*g=K'*(f'*b) from hx.symm]; unfold salary
    dsimp only
    rw [X.vents hp Q.buys u F₀.room.sight.1 R Q.table k W o.a h]; unfold f' b c' u; ring
  rw [hy]; change M.realP X (X.view u) k W* _ *g=_
  by_cases hf : g=0
  · rw [hf,mul_zero,mul_zero]; ring
  have hr := D.laws.intake
  have hu : c'=M.bill k U:=by
    unfold c' comfortP bill; split
    next =>
      unfold paidU
      have ht i : X.bag R o.a u i=R.activities.K i (X.input u) := by unfold bag; rw [X.underfoot he hf, mul_one]
      simp_rw [Leaf.paidU, Leaf.fond, X.underfoot he hf, mul_one, ht]; rfl
    rfl
  have hv : M.realP X (X.view u) k W= X.levy R * (C₁ * L*w) * c' *
      Real.exp ( (∑' i,Raw.expo T X.x R U X.V i) +
        (-R.beta*(wholeGap T X.x U X.V + ∑ i, monetary S (S.prediction U X.k) X.V i))) := by
    unfold realP levy; dsimp only; rw [Raw.fused T hr.ready, mul_right_comm (sieve ..),M.reduce X hr,M.counted hr.cap _ _ hL,hu]
    unfold C₁ L w U; simp_rw [Real.exp_add,input]; ring
  rw [hv]
  by_cases he : C₁=0
  · rw [he]; ring
  by_cases ha : L=0
  · rw [ha]; ring
  have hZ := X.unified_exp D h hk z he ha hf
  unfold ribbons deducted thetaRef
  rw [X.payment Q.table hr.positive Q.table_exists]
  have hz := congr_arg Real.exp hZ
  simp_rw [Real.exp_add] at hz
  simp_rw [Real.exp_add]
  unfold U u; unfold cross_link at hz
  linear_combination X.levy R * (C₁*L*w) * c' *g* (bell ^ Fintype.card (Tubular f G))⁻¹ * measure_g Q.table R.beta ^ Fintype.card F.Free * hz
end Team
end YM.PhysicalNext.Repeat.Lotus
