import YM.MultiNext.VACUUM_STABILITY.Arrival.Through
import YM.MultiNext.VACUUM_STABILITY.Component.FirstSum
import YM.MultiNext.VACUUM_STABILITY.Tune.Used


set_option warningAsError false

/-!
# First-system physical gate

Further upstream than Tenders.

Check these ingredients already before an unmarked vStep
callback/atom producer; per-record actual identities required, not a synthetic stencil
or condition on the unknown output path.

This theorem sums over every allowed request at exact analytic prices given
these data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Component
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Arrival Arrival.Flock Pasture Tune Tree YM.Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V I : Type} {G : Gauge} {n f : Side} {B : Brush V G n} [Fintype V]

/-- Producer has to implement for the **actual** kernel/path with input arrival
and chosen B. Ancestors associated to the component selection must record *every*
input thermal and K selection exactly; read in one sector with same tags and conditional
law (further factoring is an analytic step required for `crossing`). No prices or
summability budgets on a Reference K or log/exit or marked hierarchy assumed here. Equality
checked per actual pre-scaled monomial term (mask retained), not merely almost everywhere.
-/
structure Flow (S : StepData n f) (Y : Forest S.ratio) {x W : ℝ} (D : Allocation G S x W)
    (F : Flock V G f) (Q : Rep G f) (P : BudgetPoint) (A : Pasture I B) (back : Finset I→ Voucher F) : Prop where
  pays : B.pay = fun i => (F i).fiat
  destination (b U) : A.view P U 1 b ≠ 0 → F.signature Q (back b)=∑ i∈b,A.hue i
  crossing (b : Voucher F) (U : Config G n) : HasSum (fun i : Finset I => if back i=b then B.base U*A.view P U 1 i else 0)
        (∑ i,output D Y Q.beta (F.peelRow Q b) i U)

-- analytical projection post price

private lemma consume (S : StepData n f) (Y : Forest S.ratio) {x W : ℝ} (D' : Allocation G S x W)
    {F : Flock V G f} {Q : Rep G f} (P : BudgetPoint) (U : Config G n) {g : Config G f → ℂ} (z : V → ℂ)
    (he : HasSum (fun i : Voucher F => (payFee F z*beat (signature F Q i) z)*
      ∑ A, output D' Y Q.beta (peelRow F Q i) A U) (S.push Q.beta g U))
    {A : Pasture I B} {back : Finset I→Voucher F} (hg : Flow S Y D' F Q P A back)
    {c r κ : ℝ} (hp : A.ProductCost P z c r κ) (hk : 0 < κ) : S.push Q.beta g U=B.flush P z U := by
  have hs := A.arrives U (A.accomplish P z c r κ hp hk.le) hp.tall
  let T := payFee F z * B.base U
  let E (b : Finset I) := A.view P U z b; let E' (b : Finset I) := A.view P U 1 b
  have ht b : (payFee F z*beat (signature F Q (back b)) z)*(B.base U*E' b)=T*E b := by
    unfold E; rw [A.hues]
    change _ = T*(beat _ z*E' b)
    by_cases H : E' b=0
    · simp [H]
    rw [hg.destination b U H]; unfold T; ring
  have hu := (hs.mul_left T).tsum_fiberwise back
  have hV (i : Voucher F) : (payFee F z*beat (signature F Q i) z)*(∑ A, output D' Y Q.beta (peelRow F Q i) A U) =
      ∑' j : back ⁻¹' {i}, T*A.view P U z j.val := by
    let f b := T*A.view P U z b
    change _ = ∑' j : back ⁻¹' {i}, f j.val
    rw [_root_.tsum_subtype (back ⁻¹' {i}) f,←(hg.crossing i U).tsum_eq,←tsum_mul_left]
    apply tsum_congr; intro j
    by_cases h : back j=i
    · rw [if_pos h,Set.indicator_of_mem (show j∈back ⁻¹' {i} from h)]; exact h ▸ ht j
    simp [Set.indicator,h]
  rw [←he.tsum_eq,tsum_congr hV,hu.tsum_eq]; unfold T Brush.flush payFee; rw [hg.pays, mul_comm (Complex.exp _)]

/-- Inputs earlier in component production. Stronger output-hit `ProductCost` at each
chosen z (constant budgets symbolically uniform), firstcost alone, not stickers/higher packs.
`Footage` purchase plus actual vacuum component estimates possible sources of these numbers.
`Slicer.Landed` unavoidable reference and vacuum checkout (can show from Labels and local window
identities). -/
structure Office (S : StepData n f) (Y : Forest S.ratio) {x W : ℝ} (D' : Allocation G S x W)
    {P : Rep G n} (A : Pasture I B) (L : V→Support n→Prop) (T : Finset V) (w : V→Pulse G n)
    (s : Tune.Slicer B) (Am : Set (V→ℂ)) (χ κ : ℝ) (m : ℕ) (F : Flock V G f) (Q : Rep G f) : Prop where
  steam : ∃ back, Flow S Y D' F Q P.p A back
  tickets : s.Ticket P.p L T m χ
  stage : 1 ≤ χ
  earlier : ∀ z∈Am, A.ProductCost P.p z (Tune.Price.first P.p m χ) (Rates.inner P.p+13) κ
  reclosure : ∀ z ∈ Am, ∃ u, (∀ i, ∀ U, ‖(s.base i).stamp.tell z U‖ ≤ u i) ∧
      Ac.Hit (fun i => (s.base i).zone) P.p.B u (Rates.inner P.p) (Rates.window P.p/2)
  compatible : s.Landed P T w

/-- Exact Tenders data for the request with the charged `Scratch`s / `Credit`s.
First-system variant theorem. No assumption of post-component W/log/mixed-source
budgets. Need `Office` at these widths and per-record identities on the actual
forest/partition/branch; no weakening to ambient Taylor approximations. -/
theorem deposits (S : StepData n f) (Y : Forest S.ratio) {x W : ℝ} (D' : Allocation G S x W)
    {P : Rep G n} (A : Pasture I B) (L : V→Support n→Prop) (T : Finset V) (w : V→Pulse G n)
    (s : Tune.Slicer B) (o : V→Site n) (k : V→ℝ) (η χ κ : ℝ) (m : ℕ) (F : Flock V G f) (Q : Rep G f)
    (D : V→Pulse G f) (ht : S.patch.Branches S.kernel G) (hq : GaugeInvariant Q.exponent)
    {σ c Λ δ b : ℝ} (hQ : Q.Lawful σ c Λ δ b) (hv : Widens L) {p : ℝ} (hp : 0 < p)
    (hk : 0 < κ) (he : 0 < η) (hr : η≤1) (h : Attended F Q.p D (fun i => S.ratio.embed (o i)) k p)
    (hO : Office S Y D' (P:=P) A L T w s (allot o k η) χ κ m F Q) :
    let C := s.package P.p T
    Supported B C P.p L T ∧ Settled B C P T w ∧ ∀ z∈allot o k η,
        Quoted B C P.p κ z ∧ S.push Q.beta (perturbs Q D z)=B.flush P.p z := by
  intro C
  have he' := hO.earlier; obtain ⟨B',hB'⟩:=hO.steam
  have hh z (hz : z∈ allot o k η) : s.Endowed P.p m χ κ z := by
    obtain ⟨ha,f,hf,hF⟩:= A.accomplish _ _ _ _ _ (he' z hz) hk.le
    refine ⟨hO.stage,ha,⟨f,fun i => (hf i).2,?_⟩,hO.reclosure _ hz⟩
    have hH := (Tune.Price.enough (P:=P.p) (m:=m) hO.stage).2.1.trans (Rates.still_thin _)
    exact Absolute.relax hF (mul_le_mul_of_nonneg_left hH hk.le) (fun i => (hf i).1) (fun _ => le_rfl) (by linarith)
  obtain ⟨ha,hx,hZ⟩:= Tune.stocked s P w L T m χ κ o k η (fun i => (h.authorizations i).ok) he hv hO.tickets hh hO.compatible
  refine ⟨ha,hx,fun z hz => ⟨hZ z hz,funext fun U => ?_⟩⟩
  exact consume S Y D' P.p U z ((h.delivered Q hQ hp S ht hq D' Y (extended o S.ratio he.le hz) hr U).2)
    hB' (he' _ hz) hk
end YM.Multi.Vacuum.Component
