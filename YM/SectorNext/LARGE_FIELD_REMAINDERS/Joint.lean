import YM.Push.SECTOR_MEASURE.Oriented
import YM.SectorNext.LARGE_FIELD_REMAINDERS.RemoteGap


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# One- and all-orientation remainder receipt

Without the sieve/cutOutput, we only reserve the chart volume at t scale, per
actually used remote link. With the sieve we buy squares at any scale down to
and through beta-coupling, always on the same links. Tag likelihood and flags
intact.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

private theorem turn_one {c f : Side} {S : StepData c f} (A : Stores S) : turnStore 1 A = A := by
  have he : faces 1 f=Equiv.refl _ := by
    ext p : 1
    have hh : Face.lower p 1 (0:Site f)=p.1 := by simp [Face.lower,atFace,affine,posDir]
    have hs : p.2.rotate 1=p.2 := by
      apply Subtype.ext
      simp only [PlaqAxes.rotate,PlaqAxes.ordered,Signed.one_perm,Equiv.refl_apply]
      simp [p.2.property.le]
    change Face.send 1 0 p = _; rw [Face.send,hh, hs]; rfl
  have hb : StepData.sendBonds 1 (0:Site c)=Equiv.refl _ := by
    ext i : 1; change sendEdge 1 0 _ = i
    simp [sendEdge,affine,Step.used,posDir]
  have ht : StepData.sendSites 1 (0:Site c)=Equiv.refl _ := by
    ext i : 1; change Signed.act 1 i + 0 = i; simp
  unfold turnStore; rw [he,hb,ht]
  have h {α : Type} (F : Finset α) : F.map (Equiv.refl α).symm.toEmbedding = F := by
    ext; simp
  simp_rw [h]

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (A : Stores S)
  (U : Config G f) (k : S.Choices) (V : Config G c)

def meanCut (T : Tube G S) (x : ℝ) (V : Config G c) := averaged fun s => cutOutput T x (pull s 0 V)

def visionTotal (T : Tube G S) (x : ℝ) (V : Config G c) :=
  (∑ j : Twin c, ‖T.vision (till x) (temp x) V j‖^2)

def visionMean (T : Tube G S) (x : ℝ) (V : Config G c) := averaged fun s => visionTotal T x (pull s 0 V)

lemma visionTotal_nn (x : ℝ) : 0≤visionTotal T x V := by unfold visionTotal; positivity
lemma visionMean_nn (x : ℝ) : 0≤visionMean T x V := by
  rw [← av_const 0]; exact av_mono fun _ => visionTotal_nn ..

/-- Also works on g hard sectors with no measurability of Q under changes, so long
as these values determined as usual on their actual fields and the prerequisites hold.
Coarse-volume loss L carries site count; delay price for L even after β. -/
structure Joint (x C γ L : ℝ) : Prop where
  charts i (hi : remote A (radiusB x) i) : linking S V U i ≤ C * fiery G x S.patch.L
  single : -(L*Fintype.card (Site c)) ≤ unassigned A T x U k V
  mean : -(L*Fintype.card (Site c)) ≤ meanRest A T x U k V
  use_single : γ*linkCost A x V U + reserve T.low/2*visionTotal T x V -
    L*Fintype.card (Site c) ≤ unassigned A T x U k V + cutOutput T x V
  use_mean : γ*linkCost A x V U + reserve T.low/2*visionMean T x V -
    L*Fintype.card (Site c) ≤ meanRest A T x U k V + meanCut T x V

lemma average_one (A : Signed → ℝ) (hn : ∀ s, 0 ≤ A s) :
    (Fintype.card Signed:ℝ)⁻¹ * A 1 ≤ averaged A := by
  unfold averaged; gcongr _ * ?_; exact Finset.single_le_sum (fun s _ => hn s) (Finset.mem_univ _)

set_option maxHeartbeats 650000 in
/-- Delay before shooting. Joint physical statement anchored to checked early ports
through *each* trajectory and *their own* tags. No L gate additional to Points. -/
lemma joint_post (P : Teller G) (L : Side) (W : ℝ) (hW : 0<W) :
    ∃ (C γ : ℝ) (loss : ℝ → ℝ), 0<C ∧ 0<γ ∧ (∀ n : ℕ, Tendsto (fun x : ℝ =>
      b x^n * y G L x * loss x) atTop (𝓝 0)) ∧
      ∀ᶠ x in atTop, 0≤loss x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L = L →
      100*(1+radiusB x) ≤ c.val → P.Funds S T → ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f)
      (k : S.Choices) (V : Config G c), SliceSet S F U → Seeded A U k V x W → Alive S U k →
      Joint T A U k V x C γ (loss x) := by
  obtain ⟨C,hC,hU⟩ := outside_size P L W hW
  obtain ⟨d,hd,hT⟩ := weak_pre P
  obtain ⟨R,hR,hr⟩ := link_post P L
  obtain ⟨l,hL,hq,hs⟩ := hT L W hW
  let i := reserve P.below.clip/2
  let ε := min 1 (i/d^2)
  have hi : 0 < i := half_pos (reserve_pos _)
  have he : 0 < ε := lt_min zero_lt_one (by positivity)
  let a := min P.top.clip.direct P.bind.penalty/4
  have ha : 0<a := div_pos (lt_min P.top.clip.quadratic_pos P.bind.penalty_pos) (by norm_num)
  let F := (Fintype.card Signed:ℝ)
  have hF : 1≤F := by unfold F; exact_mod_cast Fintype.card_pos
  have hF' : 0<F := by linarith
  let J x := l x * (2*Fintype.card PlaqAxes)
  refine ⟨C,(ε*a/R)/F,J,by linarith,by positivity,fun n => ?_,?_⟩
  · have hh := (hq n).mul_const (2*(Fintype.card PlaqAxes:ℝ)); rw [zero_mul] at hh
    exact hh.congr fun x => by unfold J; ring
  filter_upwards [hs,hL,hr,hU] with x hx hl hy hv
  have hJ : 0≤J x := by unfold J; positivity
  refine ⟨hJ,?_⟩
  intro c f S T hh hp hT H A U k V hF0 hV hk
  have hf (H : Forest S.ratio) (A : Stores S) (U k V) (hF0 : SliceSet S H U)
      (hV : Seeded A U k V x W) (hk : Alive S U k) :
      -(J x*Fintype.card (Site c)) ≤ unassigned A T x U k V ∧
      (ε*a/R)*linkCost A x V U + reserve T.low/2*visionTotal T x V -
        J x*Fintype.card (Site c) ≤ unassigned A T x U k V + cutOutput T x V := by
    have he' := hx c f S T hh hp hT H A U k V hF0 hV hk
    have hJ : J x*Fintype.card (Site c)=2*l x*Fintype.card (Cell c) := by
      rw [show Fintype.card (Cell c) = Fintype.card (Site c)*Fintype.card PlaqAxes from Fintype.card_prod ..]
      unfold J; push_cast; ring
    rw [hJ]
    constructor
    · exact lower_unassigned he' hl
    have hw : ε*d^2 ≤ reserve T.low/2 := by rw [hT.low]; exact (le_div_iff₀ (show 0<d^2 by positivity)).mp (min_le_right ..)
    have ht := strengthened he' hd hl ⟨he.le,min_le_left ..⟩ hw
    let K := physical A x U (S.prediction U k) V
    have hK : (ε*a/R)*linkCost A x V U ≤ (ε*a)*K := by
      apply (mul_le_mul_of_nonneg_left (hy c f S T hh hp hT H A _ _ V hF0 hk) (by positivity : 0≤ε*a/R)).trans_eq
      change _ / R * (R*K) = _; field_simp
    rw [show (min T.high.direct S.kernel.penalty/4) = a by rw [hT.high,hT.knobs]] at ht
    apply le_trans ?_ ht; unfold visionTotal K at *
    nlinarith only [hK, mul_nonneg hl (Nat.cast_nonneg (α:=ℝ) (Fintype.card (Cell c)))]
  have hB := funds_branch hT
  let E := J x*(Fintype.card (Site c):ℝ)
  let g := ε*a/R
  let LC (s : Signed) := linkCost (turnStore s A) x (pull s 0 V) (pull s 0 U)
  have hz (s : Signed) := hf (turnForest s H) (turnStore s A) (pull s 0 U) (choice s k) (pull s 0 V)
    (turn_sliced s H U hF0) (pull_seeded s hB hV) (show Alive S _ _ by
      unfold Alive; rw [(carry s hB k U).1]; exact hk)
  obtain ⟨h1,h2⟩ := hf H A U k V hF0 hV hk
  constructor
  · exact (hv c f S T hh hp hT H A U V k hF0 hV hk).1
  · exact h1
  · change -E ≤ _; rw [← av_const (-E)]; exact av_mono fun s => (hz s).1
  · apply le_trans ?_ h2; have hq : ε*a/R/F ≤ ε*a/R := div_le_self (by positivity) hF
    linarith only [mul_le_mul_of_nonneg_right hq (linkCost_nn A x V U)]
  · unfold meanRest meanCut
    rw [← av_add]
    let C0 (s : Signed) := visionTotal T x (pull s 0 V)
    let a := reserve T.low/2
    refine le_trans ?_ (av_mono (F:=fun s => g*LC s + a*C0 s - E) (fun s => (hz s).2))
    change g/F * _ + a*visionMean T x V - E ≤ _
    have hi (u : ℝ) (v : Signed → ℝ) : averaged (fun s => u*v s) = u * averaged v := by
      unfold averaged; rw [← Finset.mul_sum]; ring
    rw [show averaged (fun s => g*LC s + a*C0 s - E) = _ from av_sub _ (fun _ => E), av_add, hi, hi, av_const]
    have hm := average_one LC fun s => linkCost_nn ..
    dsimp only [LC] at hm; rw [pull_id,pull_id,turn_one] at hm
    change F⁻¹ * linkCost A x V U ≤ averaged LC at hm
    unfold visionMean; change _ ≤ g*_ + a*averaged C0 - E
    have hb := mul_le_mul_of_nonneg_left hm (show 0≤g by unfold g; positivity)
    rw [div_eq_mul_inv]; linarith only [hb]
end YM.SectorNext.Remainder
