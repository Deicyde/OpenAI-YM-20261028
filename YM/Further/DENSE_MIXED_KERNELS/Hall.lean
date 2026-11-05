import YM.Extra.MULTISOURCE_BOUNDS.Scheme
import YM.Further.DENSE_MIXED_KERNELS.AtWork


/-!
# Earnings in System.Forward

A particular sufficient pricing protocol. Indexing/factorization & remaining
unmarked factor bounds are explicit inputs, see `Forum`/`Realizes`/
`Primitive`/`Bidding`. (No overall norm assumption on any first-system entry.)
See entry module for how these are used, some families where we get
much more of the hypotheses (regular/pigment, both sorts of saturated
packets), including the combinatoric/price gates. This file is the endpoint
at the Forward interface. These price-test data do not assert all criteria of
faithfulness of anyone's factorization/history. E.g. no multiplying amplitudes
across independent choices of a sector or a tree average is justified in
setting up these hypotheses.

Keeps all calculations at the scale where caller expects them. Phi, zeta etc
support and loss commitments of the caller not changed to volume-dependent
ones in the norms. Like Forward the auxiliary inequalities themselves can be
supplied even at just one torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Lattice RG Wilson Precision Labels Marker Overlay Extra.Multi Extra.Multi.Merger
open Port Gaussian Surface Mileage Extra.Multi.System Tree Pressure
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {V I : Type} [Fintype I] [DecidableEq V] {R : Census V} {m p N : ℕ} {d : V→ℕ}
variable {L : Bands R (C.path.rep N p m)} {L' : Bands R (C.path.rep N p (m+1))} {F : Scheme C d L}
variable {A : ChartRatio G} {H : Port A}

-- Keep width from SAME chosen fine body.
def width (C : Family G) (N p m : ℕ) := (Real.sqrt (C.path.β N p (m+1)))⁻¹
-- shorthand all fits
structure Forum {L : Bands R (C.path.rep N p m)} (F : Scheme C d L) (L' : Bands R (C.path.rep N p (m+1)))
    (I : Type) [Fintype I] (H : Port A) where
  vault : Vault I (C.path.levels.clock.op m p)
  money : Bazaar L' (C.path.levels.clock.op m p) F.marks F.vac
  r : Keys (F.marks.combine F.vac) F.reg
  k : Keys (F.marks.combine F.vac) F.hard
  usesR (i : r.used) : Stamp H vault money (r.visit i)
  usesK (i : k.used) : Stamp H vault money (k.visit i)

namespace Forum
variable (Q : Forum F L' I H)
-- supply the genuine packet inventory, not each independent vs D columns
def inventory (i : Q.k.used) := collect Q.money.flags (catalog (Q.k.visit i))

/-- Structural realization needed with this FIRST SYSTEM. Doesn't assert
anything about the analytic branch in the integral as estimates. Apply even
when later restored exponents differ; the census and same vacuum must not.
All modeled entries including zero prices must be invoiced; `used`
distinguishes the inert padding (see Keys.omits). Must still verify
locality & appropriateness of every support/label in constructing this
receipt, not a permission for dropping holes/marginal reads.

`rmatch` on the chosen full *germ*; can't recover `Regular.supBounds` from
only a masked equality or equality within the Healthy domain.

Doesn't demand any
differentiability around a flag jump on k data. -/
structure Realizes : Prop where
  trueFlags i : (Q.inventory i).Nonempty ∧ Q.inventory i ⊆ F.hard.supp i.val
  plain i : collect Q.money.flags (catalog (Q.r.visit i)) = ∅
  rmatch (i : Q.r.used) (u : Config G _) : Healthy (point C m).threshold (F.reg.supp i.val) u →
    F.reg.value i.val ∘ increment u =ᶠ[𝓝 0] (Q.vault.pour (fun j => (Q.usesR i j).value (width C N p m))) ∘ increment u
  kmatch (i : Q.k.used) (v) : F.hard.value i.val v =
    if F.hard.supp i.val ∩ RG.flags (point C m).threshold v = Q.inventory i then
      Q.vault.pour (fun j => (Q.usesK i j).value (width C N p m)) v else 0
  anchor i : F.anchors i ∈ F.reg.supp i
  localize i : LocalOn (F.reg.supp i) (F.reg.value i)
  borel i : Measurable (F.reg.value i)
  gauge i : GaugeInvariant (F.reg.value i)

/-- Genuine kernel estimates on **unmarked factors** required across *marked*
components. These include unmarked packet payments with a strong retained
reserve even before restoration. Tangent matrices are in sup color sense.
Output numerical hypotheses in `Bidding`. -/
structure Primitive (W : Oars) : Prop where
  Green (i : Q.r.used) : SizeUp (Q.usesR i) (point C m) (F.anchors i.val) (F.reg.supp i.val) (point C (m+1)).B (width C N p m) W
  rough (i : Q.k.used) : Workable (Q.usesK i) (point C m) (F.hard.supp i.val) (Q.inventory i) (width C N p m)

def power (W : Oars) (P : BudgetPoint) := Mileage.orderPrice P.order W.q
def bill (W : Oars) (P : BudgetPoint) := W.degree * power W P
def amend (H : Port A) (W : Oars) (P : BudgetPoint) := Mileage.license P.order W.q H * W.amp^power W P

def weight (W : Oars) (e : Pieces→ℝ) : F.marks.Id ⊕ F.vac.Id → ℝ :=
    W.price H Q.money (point C (m+1)).B (point C m).B (point C m).order e

lemma amend_pos (W : Oars) (H : Port A) (P : BudgetPoint) : 0 ≤ amend H W P := by
  have hx := Mileage.license_pad H P.order W.q
  unfold amend; have := W.pos; positivity

open Push.AbsoluteSums in
/-- First-system associated primitive alphabet and numerical gates still
required. `marked` needs Σ variant costs about every ACTUAL old label,
s not estimated from number of derivatives only. Vacuum tests incl
Teller geometry+gains on all their per-letter entries after any packet,
but not on integrated component estimates. -/
structure Bidding (W : Oars) (s : Scope) (t : Tariff) (φ : ℕ→ℕ) (ζ : ℕ→ℝ) : Prop where
  weak : 0<width C N p m ∧ width C N p m≤1
  holds : Real.exp (-Q.money.plain.ep) ≤ Extra.Multi.divisor C m
  geometry : ∃ r : ℕ,r+5 ≤ s.expand (year C (m+1)) ∧
    ForkShape L' (C.path.levels.clock.op m p).ratio L.origins F.marks (point C m).B r Q.money.owner
  marked : let P := point C m; let B := (point C (m+1)).B
    ∃ l : ℕ,∃ Γ : ℝ,bill W P + l ≤ φ (year C (m+1)) ∧ amend H W P*Γ ≤ quote C m t ∧
    ∀ i, SumBudget (fun j => if Q.money.owner j=i then Q.money.color j else 0)
      (Γ * (1+(coverNumber B (blocks L' i):ℝ))^l)
  clear : let P := point C m; let B := amend H W P; let L := (C.path.levels.clock.op m p).patch.L
    let eta := (hat C m)^(-ζ (year C (m+1))); let j:=bill W P
    ∃ l : ℕ,∃ C' q gain spend ε : ℝ,0≤C' ∧ Q.money.plain.Narrow F.vac.supp l P.B C' gain spend ε
      (P.supportExponent+6) ∧ Packets.fit L l P.B (P.supportExponent+6) (spend+1) gain q ∧
      B*2^j*EmptyBook.borrowed j*ε + Packets.totalCharge L (B*EmptyBook.borrowed j*C') l P.B q 0 ≤ eta
  reset : let P := point C m
    ∃ f, F.reset.Covers f 1 ∧ Ac.Hit F.reset.supp P.B f (P.supportExponent+3) ((hat C m)^(-ζ (year C (m+1))))

variable {s : Scope} {t : Tariff} {φ : ℕ→ℕ} {ζ : ℕ→ℝ}
variable {Q} {W : Oars} (h : Q.Realizes) (hp : Q.Primitive W) (hv : Q.Bidding W s t φ ζ)
variable (hx : L'.Active) {e : Pieces→ℝ} (he : Inbox L' (Extra.Multi.divisor C (m+1)) e)

include h hp hv hx he

lemma lit (i) : F.anchors i∈F.reg.supp i ∧ (point C m).Regular (F.reg.supp i) (F.reg.value i) ∧
    (point C m).supBounds (F.anchors i) (F.reg.supp i) (F.reg.value i) (Q.r.cost (Q.weight W e) i) := by
  let P := point C m
  refine ⟨h.anchor i,?_⟩
  by_cases ha : i∈Q.r.used
  · let v : Q.r.used := ⟨i,ha⟩
    have H u (hd : Healthy P.threshold (F.reg.supp i) u) : Pitch (F.reg.value i) u (P.dirBound (F.anchors i)) P.order
        (Q.r.cost (Q.weight W e) i) 1 := by
      rw [Keys.cost,dif_pos ha]
      exact ((SizeUp.use hx he (Extra.Multi.divisor_le ..) (Q.usesR v) (hp.Green v) hv.weak.1 hv.weak.2 hd).2).congr' (h.rmatch v u hd)
    exact ⟨⟨h.localize _,h.borel i,h.gauge i,fun u hu => (H u hu).smooth,fun u hu a _ hj =>
      Next.Foundations.left_has a hj (H u hu).smooth⟩,Q.r.prices (W.loads _ _ _ _ _ he.pos) _,
      fun u hu l hl hd => by simpa only [one_pow,mul_one] using! (H u hu).bounds l hl hd⟩
  rw [Q.r.omits _ ha,Keys.cost,dif_neg ha]; exact ⟨by
    refine ⟨fun _ _ _ => rfl, measurable_const, fun _ _ => rfl, fun _ _ => contDiffAt_const, fun u _ a l hl => ?_⟩
    exact Next.Foundations.left_has _ hl (f:=0) contDiffAt_const, Extra.Multi.supBounds_zero ..⟩

lemma hard : F.hard.Covers (Q.k.cost (Q.weight W e)) (Extra.Multi.divisor C m) := by
  intro i; refine ⟨Q.k.prices (W.loads _ _ _ _ _ he.pos) i, fun u => ?_⟩
  unfold Keys.cost; split
  next ha =>
    let j : Q.k.used := ⟨i,ha⟩
    rw [show F.hard.value i u=_ from h.kmatch j u]; split
    next heq => exact (Workable.use hx he (Extra.Multi.divisor_le ..) (Q.usesK j) (hp.rough j) (h.trueFlags j).1 hv.holds hv.weak.1 heq W
        (point C (m+1)).B).2
    next =>
      rw [norm_zero]; exact mul_nonneg (Extra.Multi.divisor_pos ..).le (by simpa only [Keys.cost,dif_pos ha] using!
        (Q.k.prices (W.loads _ _ _ _ _ he.pos) i : 0≤ Q.k.cost (Q.weight W e) i))
  next ha => rw [Q.k.omits _ ha,Pi.zero_apply,norm_zero,mul_zero]

omit hp h in
lemma earns_fork : Fork (bids L') (blocks L') F.marks.names F.marks.supp L.origins
    (C.path.levels.clock.op m p).ratio (s.expand (year C (m+1))) (point C m).B (point C (m+1)).B (φ (year C (m+1))) e
    (fun i => Q.weight W e (.inl i)) (quote C m t) := by
  obtain ⟨r,hr,h⟩ := hv.geometry; obtain ⟨l,X,hd,hq,ht⟩ := hv.marked
  exact spread _ hx h (point C m).B_pos Q.money.nonneg ht _ (amend_pos ..) he hr hq (zero_le_one.trans (quote_ge ..)) hd

omit hp h he hx in
lemma qualifies (e : Pieces→ℝ) : Ac.Hit F.vac.supp (point C m).B
    (fun i => Q.weight W e (.inr i)) ((point C m).supportExponent+6) ((hat C m)^(-ζ (year C (m+1)))) := by
  obtain ⟨l,D,q,gain,spend,ε,hD,h,hf,hq⟩ := hv.clear
  have he : (fun i => Q.weight W e (Sum.inr i))=Q.money.plain.rocket (amend H W (point C m))
      (bill W (point C m)) (point C m).B F.vac.supp := by
    funext i; unfold weight Oars.price; simp only [metric,Sum.elim_inr,mul_one]; rfl
  rw [he]; exact EmptyBook.lift _ _ h (amend_pos ..) hD hf hq

-- main endpoint using only primitive costs; note denominator divisor rule
-- applies in a funded system. No Mats/Makes for this h. Propagate from
-- same history/skeleton separately.
omit he in
theorem forward : System.Forward F L' s t φ ζ := by
  constructor; intro e he P Q₁ j η
  obtain ⟨X,hX,hT⟩ := hv.reset
  let w := Q.weight W e
  have hp' i : 0≤w i := W.loads _ _ _ _ _ he.pos i
  let K := F.marks.combine F.vac
  let a i := w (.inl i); let b i := w (.inr i)
  have hw : Sum.elim a b = w := by ext (i|i) <;> rfl
  refine ⟨a,b,X,Q.r.cost w,Q.k.cost w,fun i => hp' _, fun i => hp' _,hX,
    hard h hp hv hx he, earns_fork hv hx he, qualifies hv e,hT, lit h hp hv hx he,?_⟩
  rw [hw]; exact ⟨Q.r.display, Q.k.display⟩
end Forum
end YM.Further.DenseMixedKernels
