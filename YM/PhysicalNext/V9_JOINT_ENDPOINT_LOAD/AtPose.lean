import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Payable
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Terms
import YM.Progress.DIRECTED_RECIPE.Rollout
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Remit
import YM.Push.ABSOLUTE_SUMS.Omissions
import YM.Push.FREE_RESOLVENT.Fees
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Charges


/-!
# On the actual charged family: Lease AND marker event, consumed together

`Orders`, `Ancillary` are STILL INPUT OBLIGATIONS. Test any hard-flag and
smooth profile/eligibility ancestry to prove these, rather than assuming from
rewritten terms or post-integration reps. `survive`/`lights` are marker SUPPORT
requirements, *not* expecting an integral bound from the gate supplier.
See e.g. `Reading.signs` when deriving such handshake from closed tests of
awake atoms. All use one physique (both before / after returning to the Gaussian
law). No duplicated suppression inside a product or differentiation of
indicators. No claims of extension through variable partial-sector boundaries or
that this tour verifies the Bore, Roll, Support/tax, integral-domination
inputs necessary to build actual output activities. Which stencil/balls to
use for component separation/off, alignment and preserving the very same
physical reads in the extensions must still be proved in using the port.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Matrix Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Tariff Reading
open Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism AnalyticBridge.AnnulusRatioInsertions.Parade
open Push.SectorMeasure Wisps Schur
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {u : Spot d} {A : Stores S} {F : Forest S.ratio} {κ : S.Choices}
  {X : Support c} {H R K α β γ : Type} [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ]
  {l : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ} {q : Programme D b} {n : q.Run α β γ}
  {s : Seats l n} {a : Notice l} {B : Reading a n} {M : Income α β γ (H⊕R)}
  {V : Config G c} {v : Charges} {t cap θ L W : ℝ} {k : ℕ} {o : Site c}

def Growth (M : Income α β γ (H⊕R)) (s : Seats l n) (v : Charges) (o : Site c) (L : ℝ) (k : ℕ)
    (z : Curtain.Coordinates G H R) : ℝ := 3*(totalBill s v M o L k)*Moments.powers z ^ (max 1 M.plan)

def bills (_u : Spot d) (θ : ℝ) := anxious G S.patch.L d.betaHat θ d.input.beta

/-- Qualitative inputs on all the other letters incl kept-row residual combination and witnesses'
`Wakes` at their genuine threshold. Functional proof port! Does not cap their
numbers (sector identity/eligibility of a Reading is separate). -/
structure Orders (B : Reading a n) (M : Income α β γ (H⊕R)) (s : Seats l n) (v : Charges) (θ t L : ℝ)
    (o : Site c) (V : Config G c) (k : ℕ) : Prop where
  realRows (i : β) : i∈M.body → ∃ r : RowPosts c f, n.settled i=.inl r
  performed (p : Reel G H R K) : Needed l t V p → B.Wakes p V → Pose B s V p
  survive (p : Reel G H R K) : Needed l t V p → B.Wakes p V → a.imprint V p ∈ triggered M.expose (bills u θ)
  observes (p : Reel G H R K) : Needed l t V p → B.Wakes p V →
    let r := Growth M s v o L k (a.imprint V p); let test := d.out.dirBound o (G:=G); let f := B.turning p
    a.Score p V k test r ∧
    (∀ i : α, Ticket test k V (M.gate i) r (f.first i)) ∧
    (∑ i∈M.body,f.kept i V ≤ M.yen) ∧ (∀ i : β,i∉M.body → f.kept i V ≤ M.spend i) ∧
    (∀ i : β,Charge test k V r (f.kept i)) ∧ (∀ i : γ, s.tag i=none → Ticket test k V (M.wages i) r (f.optional i))

/-- Value-only port; at the very same argument when actually supported.
All intact-sector applications must first make sure guard prerequisites for
these tests remain. No requesting a V-extension for this port. -/
structure EarningsAt (B : Reading a n) (M : Income α β γ (H⊕R)) (s : Seats l n) (θ : ℝ) (V : Config G c) (p : Display G H R K) : Prop where
  realRows (i : β) : i∈M.body → ∃ r : RowPosts c f, n.settled i=.inl r
  lights  : p.2∈triggered M.expose (bills u θ)
  counts :
    (∀ i : α, ‖B.ret i V p‖ ≤ M.gate i) ∧ (∑ i∈M.body,B.logs i V p ≤ M.yen) ∧
    (∀ i : β,i∉M.body → B.logs i V p ≤ M.spend i) ∧
      (∀ i : γ, s.tag i=none → ‖B.delta i V p‖ ≤ M.wages i)

structure Ancillary (B : Reading a n) (M : Income α β γ (H⊕R)) (s : Seats l n) (θ : ℝ) (V : Config G c) : Prop where
  realRows (i : β) : i∈M.body → ∃ r : RowPosts c f, n.settled i=.inl r
  earned p : B.HeldAt V p → EarningsAt B M s θ V p

namespace Seats
variable (s v M o L k θ cap)
omit [Fintype R] [Fintype α] [Fintype β] [DecidableEq β] in
lemma first_tariff (z i) : ((hire s v M o L k θ cap).rents).portal i z = M.gate i := by
  unfold Tariff.portal Tariff.reach Install.rents; simp [hire]
omit [Fintype R] [Fintype α] [Fintype β] [DecidableEq β] in
lemma second_tariff (z i) : ((hire s v M o L k θ cap).rents).invoice i z = M.spend i := by
  unfold Tariff.invoice Tariff.reach Install.rents; simp [hire]
omit [Fintype R] [Fintype α] [Fintype β] [DecidableEq β] in
lemma tagged_other {i} (h : i∉s.big) (z) : let rc := ((hire s v M o L k θ cap).rents)
    s.tag i=none ∧ rc.quota i z = M.wages i := by
  intro rc
  have h' := h
  rw [big,Finset.mem_filter] at h
  have he : s.tag i=none := by cases hi : s.tag i <;> [rfl; exact (h ⟨Finset.mem_univ _, _,hi⟩).elim]
  exact ⟨he,(if_neg h').trans (by change s.stipend v M i = _; unfold Seats.stipend; rw [he]; rfl)⟩
end Seats

omit [Fintype α] [Fintype β] [Fintype H] [Fintype R] [DecidableEq β] [DecidableEq γ] in
lemma value_vapors (hV : At v u V k) (j : s.big) (M : Income α β γ (H⊕R)) (y : Display G H R K) :
    ‖vapors l (s.place j) V y‖ ≤ (s.stipend v M j.val)^2 * floorPrice (s.sits j.val) y.2 := by
  rw [s.sits_big, s.stipend_big v M,Seats.issued]
  cases s.place j with
  | inl i =>
    let X : Finset ((H⊕R)×G.ColorIndex) := {i,i} ×ˢ Finset.univ
    let r := ballast 1 X y.2
    let C := v.levy d.betaHat * v.price
    have hQ : 1 ≤ floorPrice X y.2 := inPrice ..
    calc
      _ ≤ ∑ b:G.ColorIndex,‖headwind d.tube d.betaHat u.A u.F u.k d.broadCut d.radius d.g (rear l y.1) V (l.slot (i,b))*y.2 (i,b)‖ := norm_sum_le ..
      _ ≤ ∑ _:G.ColorIndex, C*r := Finset.sum_le_sum fun b _=>by
        rw [norm_mul]; exact mul_le_mul ((hV.moving 0 (l.slot (i,b)) (rear l y.1)).2.base) (buoys X y.2 (by simp [X]) le_rfl) (norm_nonneg _) (by have := v.paid; exact mul_nonneg (v.levy_pos ..).le (by linarith))
      _ = ((Fintype.card G.ColorIndex:ℝ)*C)*r := by simp [mul_assoc]
      _ ≤ _ := mul_le_mul (v.solo_covers G _) (show r≤floorPrice X y.2 by unfold r ballast; rw [one_mul,Real.sqrt_le_left (by linarith)]; nlinarith) (zero_le_one.trans (buoy X y.2 le_rfl)) (sq_nonneg _)
  | inr pos =>
    rcases pos with ⟨m',⟨i,h⟩,f⟩
    let X : Finset ((H⊕R)×G.ColorIndex) := {i,h} ×ˢ Finset.univ
    let r := ballast 1 X y.2
    let C := blockPrice v u.A u.F G d.betaHat (m'+1) (l.read i) f (l.read h)
    have hr : 0 ≤ r := zero_le_one.trans (buoy X y.2 le_rfl)
    calc
      _ ≤ ∑ a:G.ColorIndex, ‖∑ b:G.ColorIndex, y.2 (i,a)*(block d.tube u.A u.F d.betaHat u.k (m'+1) (l.read i) f (l.read h) a b V * y.2 (h,b)) / 2‖ := norm_sum_le ..
      _ ≤ ∑ _:G.ColorIndex, ∑ _:G.ColorIndex,r*(C*r) := by
        refine Finset.sum_le_sum fun a _ => (norm_sum_le ..).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_div]; apply le_trans (div_le_self (norm_nonneg _) (by norm_num))
        simp only [norm_mul]; exact mul_le_mul (buoys X y.2 (by simp [X]) le_rfl) (mul_le_mul (hV.block_ticket _ _ _ _ _ _ 0).base
          (buoys X y.2 (by simp [X]) le_rfl) (norm_nonneg _) (blockPrice_nn ..)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr
      _ = (Fintype.card G.ColorIndex:ℝ)^2*C* r^2 := by simp; ring
      _ ≤ _ := by unfold r; rw [ballast_sq, one_pow,one_mul]; exact mul_le_mul_of_nonneg_right (v.walk_covers ..) (zero_le_one.trans (inPrice ..))

section enters
variable (h : Limits v S.patch G cap d.betaHat) (hC : u.Clearing V) (hM : Peak (u.C V) cap)
    (hV : At v u V k) (hp : 0<θ) (hb : 0<d.input.beta)
include h hC hM hV hp hb

omit hV hM hC in
theorem orders_partial {ok : u.ActiveKey → Prop} (hx : Part ok v d.radius d.tube u.k V d.out k d.broadCut d.g)
    (hl : (a.C V).PosDef) (he : Peak (a.C V) cap)
    (hh : ∀ i, ok (l.read i)) (hw : ∀ j : s.big, ∀ n (i h : H⊕R) (f : Tracks u.ActiveKey n), s.place j=Sum.inr ⟨n,(i,h),f⟩ → ∀ t,ok (f t)) (ho : Orders B M s v θ t L o V k) (hs : Studio d.chart t k L W) :
    let Q := hire s v M o L k θ cap
    B.Clearance t Q.rents V (d.out.dirBound o) k := by
  intro Q
  refine ⟨hl,he,s.lease v M h,ho.realRows,fun p ht he => ?_⟩
  let E := Q.rents; let z := a.imprint V p; let w := d.out.dirBound o (G:=G); let f := B.turning p
  obtain ⟨hA,hα,hy,hS,hβ,hγ⟩ := ho.observes p ht he
  have h1 i : Ticket w k V (E.portal i z) (E.grow z) (f.first i) := by rw [show E.portal i z = M.gate i from s.first_tariff ..]; exact hα i
  have h2 i : Ticket w k V (E.quota i z) (E.grow z) (f.optional i) := by
    by_cases hB : i∈s.big
    · exact (ho.performed p ht he).billed_local M hh hx hs ht i hB (hw ⟨i,hB⟩)
    obtain ⟨h₁,h₂⟩ := s.tagged_other M v cap θ L k o hB z
    rw [show E.quota i z = _ from h₂]; exact hγ i h₁
  have hEntered := (s.enters v M (L:=L) (k:=k) (o:=o) h hb hp z).2.1 (ho.survive p ht he)
  refine ⟨⟨⟨fun i => (h1 i).base,fun i => (h2 i).base,hy,fun i hi=>?_,hEntered⟩,h1,hβ,h2⟩,hA⟩
  rw [s.second_tariff]; exact hS _ hi

/-- Exact, true-law Clearance, under remaining field/read/context bills, including only proper combined row costs.
No joint Z-ratio load or individual Z-ratio prices in those bills.
-/
theorem orders (ho : Orders B M s v θ t L o V k) (hs : Studio d.chart t k L W) :
    let Q := hire s v M o L k θ cap
    B.Clearance t Q.rents V (d.out.dirBound o) k :=
  orders_partial h hp hb (ok:=fun _=>True) (hV.parts _) (a.principal V hC) (a.priceCap V hC hM) (fun _=>trivial) (fun _ _ _ _ _ _ _=>trivial) ho hs

omit hM [Fintype α] [Fintype β] [DecidableEq β] in
lemma earns {p : Display G H R K} (hQ : Terms s V) (ho : EarningsAt B M s θ V p) (o : Site c) (L : ℝ) (hu : u=spectacle d A F κ) :
    Earn (B.marked V) p (hire s v M o L k θ cap).rents p.2 := by
  let Q := hire s v M o L k θ cap
  obtain ⟨hα,hS,hβ,hγ⟩ := ho.counts
  have hh (i : γ) : ‖B.delta i V p‖ ≤ Q.rents.quota i p.2 := by
    by_cases hi : i∈s.big
    swap
    · obtain ⟨h1,h2⟩ := s.tagged_other M v cap θ L k o hi p.2; rw [show Q.rents.quota i p.2 = _ from h2]; exact hγ i h1
    rw [hQ.spells hV hu hC B (s.place_is ⟨i,hi⟩),show Q.rents.quota i p.2=_ from if_pos hi]
    exact value_vapors hV ⟨i,hi⟩ M p
  refine ⟨fun i=>?_,hh,hS,fun i hi=>?_,(s.enters v M h hb hp p.2).2.1 ho.lights⟩
  · rw [s.first_tariff]; exact hα i
  rw [s.second_tariff]; exact hβ _ hi

theorem rough (hQ : Terms s V) (ho : Ancillary B M s θ V) (o : Site c) (L : ℝ) (hu : u=spectacle d A F κ) :
    B.Rough V (hire s v M o L k θ cap).rents :=
  ⟨a.principal V hC,a.priceCap V hC hM,s.lease v M h,ho.realRows,fun p ht => earns h hC hV hp hb hQ (ho.earned p ht) o L hu⟩
end enters
end YM.PhysicalNext.JointLoad
