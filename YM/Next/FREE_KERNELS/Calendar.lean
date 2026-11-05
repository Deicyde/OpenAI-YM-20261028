import YM.Next.FREE_KERNELS.Rack
import YM.Work.B04

/-!
# Retarget unused Sheet numbers before Rolls (linear node **only**)

The committed common K-prices from F09 services depend, in the typed
instance, on P. Important caveat in using that quantifier at RRequirements:
may need other stage rates after pricing T but still before Rolls. Permit a
caller to use a preliminary cheap P Sheet for the linear pricing. Show
exactly what sufficient comparisons then support using price/T on a later
Sheet. Clips need only agree on the **direct** coefficient (the only one in
Floor etc). The *logCost* & drift gate comparisons below are only numerical,
required here so using the proxy Sheet doesn't assume existence of a
calendar, and easily priced in the actual profile if necessary. No impact on
waits/per-periods/producers from other nodes is claimed. Application keeps
the SAME schedule, charts, threshold-independent of path fields etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG RG.Supply Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {G : Gauge}

def numericBasis (p : Stage) := Real.log (1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent)

def Willing (p q : Stage) := p.clip.direct=q.clip.direct ∧ p.drift≤q.drift ∧ numericBasis p≤numericBasis q

variable (P : Sheet G) (A : Levels G) (h : ∀ i, Willing (P.profile i) (A.clock.stage i))
/-- No fake choices supplied to *final* nonlinear callers. This is an
auxiliary adapter SOLELY to price before those choices. -/
def payCalendar : Calendar G := { A.clock with stage:=P.profile }
def usingPrices : Levels G where
  clock := payCalendar P A
  blocks := fun i j => ⟨(A.blocks i j).branches,(A.blocks i j).symmetric,(A.blocks i j).gauge⟩
  fits := by
    let C := payCalendar P A
    have hh (i : ℕ) := h (A.clock.J (i+1))
    have hu (i : ℕ) : 0 ≤ Real.log (A.S.block i).val := Real.log_nonneg (by exact_mod_cast (A.S.block i).property)
    let g := A.fits
    exact {
      mesh := g.mesh
      sameFactor := g.sameFactor
      monotoneL := g.monotoneL
      mono := g.mono
      stepSlow := g.stepSlow
      deep := g.deep
      deepOrder := fun i j hij => P.orders (g.mono hij)
      deepPower := fun i j hij => P.powers (g.mono hij)
      deepExp := fun i j hij => P.prices (g.mono hij)
      delayed := g.delayed
      smallField := g.smallField
      sizeT := g.sizeT
      fitsPatch := g.fitsPatch
      thetaRange := g.thetaRange
      thetaMono := g.thetaMono
      driftSmall := fun i => (div_le_div_of_nonneg_right (hh i).2.1 (hu i)).trans (g.driftSmall i)
      logCost := fun i => (div_le_div_of_nonneg_right (hh i).2.2 (hu i)).trans (g.logCost i) }

lemma direct_retarget (i : ℕ) : ((usingPrices P A h).params i).clip.direct=(A.params i).clip.direct := (h _).1
lemma location_used (d i : ℕ) : flying (usingPrices P A h) d i=flying A d i := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    rw [flying, flying, ih]
    rfl

lemma floor_direct {p q : Clip} (he : p.direct=q.direct) {M : Bed} {n η C} (h : Floor M p n η C) : Floor M q n η C := by
  have hh : M.full p n=M.full q n := by unfold Bed.full; rw [he]
  exact {h with roots := hh ▸ h.roots}
lemma roll_direct {q q' p p' : Clip} (h : p.direct=p'.direct) (g : q.direct=q'.direct) {c f : Side}
    {S : StepData c f} {X Y : Bed} {A : Towers S.patch.L} (hx : Towers.Roll S X Y A p q) : Towers.Roll S X Y A p' q' := by
  have hh : X.full p f=X.full p' f := by unfold Bed.full; rw [h]
  have hu : Y.full q c=Y.full q' c := by unfold Bed.full; rw [g]
  refine { hx with n:=hu ▸ hx.n, nPart:=hu ▸ hx.nPart,oPart:=hu ▸ hx.oPart,fPart:=?_, orthogonal:=hh ▸ hx.orthogonal }
  rw [← hh,← hu]; exact hx.fPart

def recopy (M : Horizon (usingPrices P A h)) : Horizon A := ⟨M.H,M.towers⟩
lemma direct_recopies {X Y : MapPrices} (l : ℕ → ℝ) (M H : Horizon (usingPrices P A h))
    (hh : Rack (usingPrices P A h) X M ∧ Present (usingPrices P A h) M l ∧ Retained H M ∧ H.Suffices Y) :
    let U := recopy P A h M; let V := recopy P A h H
    Rack A X U ∧ Present A U l ∧ Retained V U ∧ V.Suffices Y := by
  intro U V; obtain ⟨hq,hu,hs,hv⟩ := hh
  refine ⟨⟨hq.covers,fun N i he n => floor_direct (direct_retarget P A h i) (hq.traces N i he n),hq.oath,hq.top,hq.legs,hq.crosses,hq.creak⟩,?_,hs,
    hv.rows,fun N i he n => floor_direct (direct_retarget P A h i) (hv.all N i he n),hv.costs,hv.crossings,fun N i p hi => roll_direct (direct_retarget P A h (i+1)) (direct_retarget P A h i) (hv.stack N i p hi),hv.top⟩
  have he (N m : ℕ) : location (usingPrices P A h) N m=location A N m := location_used P A h _ _
  have hh (N m : ℕ) : destination (usingPrices P A h) N m=destination A N m := by unfold destination; rw [he]; rfl
  refine ⟨fun N i hi => ?_,fun N i hi => ?_⟩
  · have hb := hu.1 N i hi; rw [he] at hb; exact hb
  have hb := hu.2 N i hi; unfold destination stageHop at hb; rw [he] at hb; exact hb

/-- Alarm budgets under Paid are numerically sufficient for the linear
Calendar inputs at exactly those steps. -/
lemma credit_from_sheet {P' : Sheet G} {D : Rolls P'} {W : Protection D} {f : Delays W} {Y : Bar f} {U : Wait Y} {A : Levels G}
    (ha : Paid U A) (γ b) (hk : ∀ i, P'.first ≤ i → (P'.profile i).clip.direct ≤ γ i)
    (hl : ∀ i, P'.first ≤ i → b i≤P'.floorL i) : Credit A γ b := by
  have hj m : P'.first ≤ A.clock.J m := ha.firstZero ▸ A.fits.mono (Nat.zero_le m)
  constructor
  · intro i; have he := hk _ (hj i); rw [← ha.stage] at he; exact he
  intro i
  rw [← A.fits.sameFactor i,ha.lengths]; exact (hl _ (hj _)).trans (D.large _).need

/-- A cross-node consumer. P potentially preliminary with cheap stage
prices, then P' budgets paid/rolled. Never take L into pricing T. Works
for **any** Wait/Paid inputs and all periods. `P=P'` of course simplest.
-/
theorem before_paid (K : KernelChoices) :
    ∃ X l γ b,Catalog K X l γ b ∧ ∀ P : Supply.Sheet G, P.kernel=K →
    ∃ T : MapPrices, ∀ (P' : Sheet G), P'.kernel=P.kernel → (∀ i,Willing (P.profile i) (P'.profile i)) →
      (∀ i,P'.first ≤ i → (P'.profile i).clip.direct ≤ γ i) → (∀ i,P'.first ≤ i → b i ≤ P'.floorL i) →
      ∀ (D : Rolls P') (W : Protection D) (Y : Delays W) (p : Bar Y) (L : Wait p) (A : Levels G), Paid L A →
      ∃ M H : Horizon A, Craft.Rack A X M ∧ Present A M l ∧ Bid.Retained H M ∧ H.Suffices T ∧
        Present A H l ∧ ∀ N m n, m≤N → Bid.Sworn (H.H N m) n G := by
  obtain ⟨X,l,γ,b,h,hT⟩ := retained_support (G:=G) K
  refine ⟨X,l,γ,b,h,fun P hp => ?_⟩
  obtain ⟨T,hT⟩ := hT P hp; refine ⟨T,fun P' hp' H hγ hb D W Y p L A hA => ?_⟩
  have he i : Willing (P.profile i) (A.clock.stage i) := by rw [hA.stage]; exact H i
  have hc := credit_from_sheet hA γ b hγ hb
  let f := usingPrices P A he
  have hb : Credit f γ b := ⟨fun i => (direct_retarget P A he i).trans_le (hc.1 i),hc.2⟩
  obtain ⟨M,Q,hm,hp,hq,hr,-⟩ := hT f (hA.kernel.trans hp') rfl hb
  obtain ⟨h₁,h₂,h₃,h₄⟩ := direct_recopies P A he l M Q ⟨hm,hp,hq,hr⟩
  exact ⟨_,_,h₁,h₂,h₃,h₄,retained_presents _ _ _ _ h₂ h₁ h₃⟩
end YM.Next.Free

/-! ## An isolated issuer with no nonlinear affordability claim -/
namespace YM.Next.Free
open Filter Set Function Lattice Bloch Metric Exterior Precision RG RG.Supply Bid Craft
open scoped Topology BigOperators ComplexConjugate
variable {G : Gauge}




end YM.Next.Free
