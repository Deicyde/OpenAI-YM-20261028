import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Freight
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Horizontal


/-! # Charge the two lists after mounting in signed channels

The flags tested by these functions are evaluation-only here; don't reuse locals
at this support without the halo when integrating. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Lattice RG Wilson Finset WardBin Push.AbsoluteSums UVNext.PricedKernels
open scoped BigOperators Matrix.Norms.Frobenius Topology ContDiff Classical
variable {G : Gauge} {n : Side} (P : PathData G) (p : Clip) (b : BudgetPoint)

def young (i : Card n) := i.read (raw P p i.token)
def tuned (i : Card n) := i.read (response P p i.token)
def attachedClip (i : Card n) := i.read (literal P p b i.token)
def framed (i : Card n) := masked b.threshold (cardSite P b i).support (young P p i)
def narrow (i : Card n) := masked b.threshold (ringlet i.1) (tuned P p i)
def broad (i : Card n) := masked b.threshold (cardSite P b i).support (tuned P p i)

-- agree with their particular canonical-mask budgets

def priceY (j : Sequence) := (Wheels.tariff b*b.threshold^2)*priceRaw P p b j
def priceT (j : Sequence) := (Wheels.tariff b*b.threshold^2)*priceResponse P p b j

lemma young_local (i : Card n) : b.Regular (cardSite P b i).support (young P p i) ∧
    b.supBounds (cardSite P b i).site (cardSite P b i).support (young P p i) (priceY P p b i.token) := by
  have hh := raw_reg (n:=n) P p b i.token; have he := bill_raw (n:=n) P p b i.token
  refine ⟨Wheels.regular_carry i.turns i.atPin hh,?_⟩
  unfold priceY; rw [show _*priceRaw P p b i.token=Wheels.tariff b*(priceRaw P p b i.token*b.threshold^2) by ring]
  have hx := Wheels.carry_bound i.turns i.atPin hh (sup_of_bill he); rw [i.pull_home] at hx; exact hx

lemma tuned_local (i : Card n) : b.Regular (ringlet i.1) (tuned P p i) ∧
    b.supBounds (cardSite P b i).site (ringlet i.1) (tuned P p i) (priceT P p b i.token) := by
  have hh:=response_reg (n:=n) P p b i.token; have he:=bill_response (n:=n) P p b i.token
  have hs := Wheels.regular_carry i.turns i.atPin hh; have hx := Wheels.carry_bound i.turns i.atPin hh (sup_of_bill he)
  rw [← ringlet_turn,i.pull_home] at hs; rw [← ringlet_turn,i.pull_home] at hx
  unfold priceT; rw [show _*priceResponse P p b i.token=Wheels.tariff b*(priceResponse P p b i.token*b.threshold^2) by ring]
  exact ⟨hs,hx⟩


/-- Log of the *multiplier* attaching on failed flag. -/
def refund (α ε : ℝ) (i : Card n) (U : Config G n) := (α+ε)*(attachedClip P p b i U - framed P p b i U) +
    ε*(broad P p b i U - narrow P p b i U)

def coverCharge (α ε : ℝ) (i : Sequence) := |α+ε| * (priceClip P p b i+priceY P p b i) + |ε| *(2*priceT P p b i)

def residue (ε : ℝ) (i : Card n) := ε • (tuned P p i-young P p i)

def skeletonCharge (ε : ℝ) (i : Sequence) := |ε| *(priceY P p b i+priceT P p b i)

lemma anchorsPay (hs : G.Simple) (hn : 2 ≤ n.val) (ε : ℝ) (i : Card n) :
    let X := (cardSite P b i).support
    let E := residue P p ε i
    b.Regular X E ∧ b.supBounds i.1 X E (skeletonCharge P p b ε i.token) ∧ E 1=0 ∧
      (Nonwrapping X i.1 → ∀ u v, IsAffineDirection i.1 u → IsAffineDirection i.1 v → logHessian E u v=0) := by
  intro X E
  obtain ⟨ht,hT⟩:=tuned_local P p b i; obtain ⟨hy,hY⟩:=young_local P p b i
  have hr := reg_extend ht (petal P b i)
  refine ⟨reg_scale ε (reg_sub hr hy),?_,?_,?_⟩
  · unfold skeletonCharge; rw [add_comm]; exact sup_scale ε (sup_sub hr hy (sup_extend hT (petal P b i)) hY)
  · simp only [E,residue,Pi.smul_apply, Pi.sub_apply,young,tuned,Around.read,pull_empty,
      (stub (n:=n) P p i.token).1,(stub (n:=n) P p i.token).2,sub_zero, smul_zero]
  intro he u v hu hv; obtain ⟨a,d,ha⟩:= onStencil_of_affine hu X; obtain ⟨c,e,hc⟩:=onStencil_of_affine hv X
  rw [log_eq_H]; change H (residue P p ε i) u v=_
  rw [residue,scalar_jet (reg_sub hr hy),sub_jet hr hy,show H (young P p i) u v=H (tuned P p i) u v from cardResponds P p b hn i hs he ha hc,sub_self,mul_zero]

lemma refund_cost (α ε : ℝ) (i : Card n) (U : Config G n) : |refund P p b α ε i U| ≤ coverCharge P p b α ε i.token := by
  obtain ⟨_,hh⟩:= tuned_local P p b i
  have hk : |broad P p b i U|≤priceT P p b i.token := mask_cost (sup_extend hh (petal P b i)) U
  have ht : |narrow P p b i U|≤priceT P p b i.token := mask_cost hh U
  unfold refund coverCharge
  apply le_trans (abs_add_le ..)
  rw [abs_mul,abs_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left ((abs_sub ..).trans
    (add_le_add (clip_claim P p b _ (pull _ _ U)) (mask_cost (young_local P p b i).2 U))) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left ((abs_sub ..).trans ((add_le_add hk ht).trans_eq (by ring))) (abs_nonneg _))

lemma shield (h : Selector p b) (U : Config G n) (i : Card n) (hh : Healthy b.threshold (cardSite P b i).support U) :
    attachedClip P p b i U = framed P p b i U ∧ broad P p b i U=narrow P p b i U := by
  refine ⟨?_,?_⟩
  · rw [framed,masked_eq _ _ _ _ hh]
    exact literal_here P p b h _ _ ((Wheels.safe i.turns _ _).1 hh)
  rw [broad,narrow,masked_eq _ _ _ _ hh,masked_eq _ _ _ _ (Disjoint.mono_left (petal P b i) hh)]
lemma refund_visits (h : Selector p b) (U : Config G n) (i : Card n) (hh : Healthy b.threshold (cardSite P b i).support U)
    (α ε : ℝ) : refund P p b α ε i U=0 := by
  obtain ⟨he,hb⟩:=shield P p b h U i hh; simp only [refund,he,hb,sub_self,mul_zero,add_zero]

lemma respects (h : Selector p b) (α ε : ℝ) (i : Card n) : GaugeInvariant (refund P p b α ε i) ∧
    Measurable (refund P p b α ε i) ∧ UsesFinal b.threshold (cardSite P b i).support (refund P p b α ε i) := by
  obtain ⟨hx,_⟩:=young_local P p b i; obtain ⟨hh,-⟩:= tuned_local P p b i
  have hk:= reg_extend hh (petal P b i)
  have hc : GaugeInvariant (attachedClip P p b i) := Wheels.trans_gauge i.turns i.1 (literal_symm P p b i.token)
  refine ⟨fun u U=>?_,?_,fun U V he he' =>?_⟩
  · simp only [refund,broad,narrow,framed,hc u U,stencil_gi hx.symmetry _ _ u U,stencil_gi hh.symmetry _ _ u U]
  · exact (measurable_const.mul (((literal_meas P p b i.token).comp (continuous_pull _ _).measurable).sub
      (masked_measurable _ _ _ hx.borel))).add (measurable_const.mul ((masked_measurable _ _ _ hk.borel).sub (masked_measurable _ _ _ hh.borel)))
  have hv : LocalOn ((cardSite P b i).support:Set (Site n)) (attachedClip P p b i) := Wheels.trans_local i.turns i.1 (literal_local P p b h i.token)
  rw [refund,refund,framed,hv U V he,
      show masked b.threshold (cardSite P b i).support (young P p i) U=framed P p b i V from stencil_reads _ hx.sites _ U V he he',
      show broad P p b i U=broad P p b i V from stencil_reads _ hk.sites _ U V he he',
      show narrow P p b i U=narrow P p b i V from Work.H03.reads_larger (petal P b i) (stencil_reads _ hh.sites _) U V he he']; rfl

lemma card_smuggle (s : Signed) (x : Site n) (i : Card n) (V : Config G n) (α ε : ℝ) : let j := Around.move _ s x i
    (cardSite P b j).site=affine s x (cardSite P b i).site ∧ (cardSite P b j).support=(cardSite P b i).support.image (affine s x) ∧
      residue P p ε j V=residue P p ε i (pull s x V) ∧ refund P p b α ε j V=refund P p b α ε i (pull s x V) := by
  intro j
  have hh : (cardSite P b j).support=(cardSite P b i).support.image (affine s x) := Around.carries ..
  have hy : young P p j V=young P p i (pull s x V) := Around.read_move ..
  have ht : tuned P p j V=tuned P p i (pull s x V) := Around.read_move ..
  refine ⟨rfl,hh,by rw [residue,residue]; simp only [Pi.smul_apply,Pi.sub_apply,hy,ht],?_⟩
  simp only [refund,narrow,broad,framed]
  rw [show attachedClip P p b j V=attachedClip P p b i (pull s x V) from Around.read_move ..,hh,
    mask_cov _ s x V hy.symm,mask_cov _ s x V ht.symm,show ringlet j.1=(ringlet i.1).image (affine s x) from ringlet_turn ..,
    mask_cov _ s x V ht.symm]

/-- Note tariff multiplies the price (even though original derivative convention
already allowed a pull, this accounts querying the same p in raw coordinates).
Values of functions from definition of `Grace`. -/
def stapleY (G : Gauge) (p : Clip) (b : BudgetPoint) (σ C : ℝ) :=
    Fintype.card Signed*((Wheels.tariff b*b.threshold^2)*rawFee G b p σ C)
def stapleT (G : Gauge) (p : Clip) (b : BudgetPoint) (C : ℝ) := Fintype.card Signed*((Wheels.tariff b*b.threshold^2)*responseFee G b p C)
def stapleC (p : Clip) (b : BudgetPoint) (C : ℝ) := Fintype.card Signed*clipFee b p C

variable {G : Gauge} {P : PathData G} {p : Clip} {b : BudgetPoint} {σ C Λ : ℝ}
private lemma mounted {c : Sequence → ℝ} {u : ℝ} (hh : SumBudget (fun i => b.mass (imageOf (n:=n) P b i) (c i)) u) :
    Sealed b (cardSite (n:=n) P b) (fun i => c i.token) (Fintype.card Signed*u) := by
  intro x
  apply stamped (w:=fun i : Card n => b.mass (cardSite P b i).support (c i.token)) _ x
  intro o s
  have he i : coverNumber b.B (cardSite P b (o,s,i)).support=coverNumber b.B (imageOf (n:=n) P b i) :=
    Push.Local.cover_map (Push.Local.turnSites s o) (Push.Local.turn_sep s o) _ _
  simp only [BudgetPoint.mass,he]; exact hh
private lemma rootedPrice (c : Sequence→ℝ) (d u : ℝ) (hd : 0 ≤ d) (h : SumBudget (fun i => b.mass (imageOf (n:=n) P b i) (c i)) u) :
    Sealed b (cardSite (n:=n) P b) (fun i => d*c i.token) (Fintype.card Signed*(d*u)) := by
  refine mounted (c:=fun i=>d*c i) ?_
  convert budget_scale hd h using 1; ext1; dsimp [BudgetPoint.mass]; ring

lemma shelfY (hd : P.Bounds p σ C Λ) (hh : Grace p b σ) :
    Sealed b (cardSite (n:=n) P b) (fun i => priceY P p b i.token) (stapleY G p b σ C) := rootedPrice _ _ _
  (mul_nonneg (Wheels.tariff_positive b).le (pow_nonneg b.threshold_pos.le _)) (raw_reserve hd hh)
lemma shelfT (hd : P.Bounds p σ C Λ) (hh : Grace p b σ) :
    Sealed b (cardSite (n:=n) P b) (fun i => priceT P p b i.token) (stapleT G p b C) := rootedPrice _ _ _
  (mul_nonneg (Wheels.tariff_positive b).le (pow_nonneg b.threshold_pos.le _)) (response_reserve hd hh)
lemma shelfClip (hd : P.Bounds p σ C Λ) (hh : Grace p b σ) :
    Sealed b (cardSite (n:=n) P b) (fun i => priceClip P p b i.token) (stapleC p b C) := mounted (clip_reserve hd hh)
end YM.AnalyticBridge.CouplingShape
