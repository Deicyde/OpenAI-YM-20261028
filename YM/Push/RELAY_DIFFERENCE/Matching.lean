import YM.Push.RELAY_DIFFERENCE.Estimate
import YM.Push.RELAY_DIFFERENCE.Subtraction
import YM.Work.G09


/-!
# A cutoff match and the price of its signed singleton

Accountable prerequisites for . Use with an equation cylinder,
the literal same weight-w primary, or the heighten comparison. All use
`Solo` in their **comparison weight** e. Proof of this part will need
one-source producers: see Encoded & LocalBounds (includes the additional
canonical/error majorants on the SIGNED step; DON'T try to deduce from
the separate materialized representations via triangle after running).
No assumption of a rent or moment estimate from that producer. Gives
the match working row, its dollar and the discounted envelopes to spend
in the multi-source problem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Bid Source
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {C : Family G} {N p m k e : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C}

def weight (C : Family G) (e m : ℕ) : ℂ := (C.S.a m : ℂ)^e

/-- Origin source propagating on C at comparison weight e. Include N,p in
every receipt (using `(N,p)` also for the envelopes). No meaningful proofs
required at skipped cutoffs by definition. `deltaFee` is only used below N.
-/
structure Solo (C : Family G) (F : Trial C) (e : ℕ) where
  source (N p i : ℕ) : Coefficient (C.labels.level e) (C.side i p)
  ticket (N p i : ℕ) : ℝ
  deltaFee (N p i : ℕ) : ℝ
  total : Cutoffs → ℝ

namespace Solo
variable (S : Solo C F e)

def row : Rowe C e := fun i => (S.source i.1 i.2 (C.ref e)).x
def top (i : Cutoffs) := (C.factory e i.1 i.2).terminal.symm (S.row i)
def column (N p i : ℕ) := (C.factory e N p).entries i (S.top (N,p))
def diff : Trial C := upper C S.row - F

def uniform (i : Cutoffs) := 4*(1+(C.path.levels.params i.1).columns)*S.total i

def primaryBill (N p i : ℕ) := (C.path.levels.params i).columns * (C.labels.level e).coeffSize
        ((C.labels.level e).core (S.column N p i).x)
def duet (N p : ℕ) : Duet C.path (C.labels.level e) N p (C.ref e) N where
  voice i := combine (S.column N p i) (S.source N p i)
  atPoint _ := 0
  cost i := if i=N then S.primaryBill N p i+S.ticket N p i else S.deltaFee N p i

/-- Supplies normalized-source step identities *at density level* on full
configuration spaces including all tags in push. All bounds on true reps,
not projection size at a test measure. Budgets needed eventual N. -/
structure Encoded (N p : ℕ) : Prop where
  active : C.ref e ≤ N
  valid i : C.ref e ≤ i → i ≤ N → (S.source N p i).Format 0 C.params (C.path.rep N p i)
  cap i : C.ref e ≤ i → i ≤ N → (S.source N p i).remBound 0 (C.path.rep N p i)
    (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (S.ticket N p i)
  put (U) : (S.source N p N).density 0 (C.localSection e) (C.path.rep N p N) U =
      weight C e N * (bare (C.beta N p) U : ℂ) * F N p 0 U
  step (i) : C.ref e ≤ i → i < N →
      (S.source N p i).density 0 (C.localSection e) (C.path.rep N p i) =
        ((C.S.block i).val : ℂ)^e • (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
          ((S.source N p (i+1)).density 0 (C.localSection e) (C.path.rep N p (i+1)))
  positive : 0 < S.total (N,p)
  afford : S.ticket N p N + (C.labels.level e).coeffSize (S.source N p N).x ≤ S.total (N,p)

/-- One-step PSREC-type majorants (both parts of `direction`).

On the **chosen**
source (incl column S.top), their literal signed budgets `deltaFee`/initial
fee, not existence of a matched hierarchy or its downward attenuation.

`deltaFee` may vary; `income` bounds actual signed components, not a norm
of a chosen unlabelled rewrite.

Need fund even transitions. -/
structure LocalBounds (W : Worth) (N p : ℕ) : Prop where
  income (i : ℕ) : C.ref e ≤ i → i < N → ((S.duet N p).voice i).remBound 0 (C.path.rep N p i)
    (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (S.deltaFee N p i)
  one (i : ℕ) : C.ref e ≤ i → i < N → let P := S.duet N p; direction C.path W i (C.labels.level e)
      (P.voice i).x (P.voice (i+1)).x (P.cost i) (P.cost (i+1))

end Solo

private lemma cap_price {n : Side} {H : Labels.Frame G e} {P : Coefficient H n} {κ p : ℝ} {s : Site n} {B : Rep G n}
    (h : P.remBound s B κ p) : 0 ≤ p := by
  obtain ⟨a,b,ha,hb,he,-⟩ := h; exact (add_nonneg ha hb).trans he

section Norm
variable (H : Labels.Frame G e) (x y : H.Coeff)
lemma plus_coords : H.coeffSize (x+y) ≤ H.coeffSize x + H.coeffSize y := by
  unfold Labels.Frame.coeffSize
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => norm_add_le ..

lemma core_price : H.coeffSize (H.core x) ≤ H.coeffSize x := by
  unfold Labels.Frame.coeffSize
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖(Function.update x 0 0) i‖ ≤ _
  by_cases h : i=0 <;> simp [h]

lemma coeff_pos : 0 ≤ H.coeffSize x := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
lemma norm_cost : ‖x‖ ≤ H.coeffSize x := by
  refine (pi_norm_le_iff_of_nonneg (coeff_pos H x)).mpr fun i => ?_
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
end Norm

namespace Solo
variable {S : Solo C F e} (h : S.Encoded N p) (hc : C.Makes)

include hc h in
lemma Encoded.both {i : ℕ} (hr : C.ref e ≤ i) (hi : i ≤ N) :
    let H := C.path.rep N p i
    (S.column N p i).Format 0 C.params H ∧
    (S.column N p i).remBound 0 H (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (S.primaryBill N p i) := by
  have H := hc.calibrated e N p h.active
  exact ⟨H.format i hr hi (S.top (N,p)),H.cap i hr hi _⟩

include hc h in
lemma Encoded.sub {i : ℕ} (hr : C.ref e ≤ i) (hi : i ≤ N) :
    let R := C.path.rep N p i
    let X := C.localSection e
    ((S.duet N p).voice i).density 0 X R =
      (S.column N p i).density 0 X R - (S.source N p i).density 0 X R := by
  obtain ⟨ha,hb⟩ := h.both hc hr hi
  exact combo_density ha (h.valid i hr hi) hb (h.cap i hr hi) (hc.wilson.represents _ p _ hi).good _

include hc h in
/-- The genuine discrepancy one-source read in exactly weight e. -/
theorem Encoded.difference (U) :
    ((S.duet N p).voice N).density 0 (C.localSection e) (C.path.rep N p N) U =
        weight C e N * (bare (C.beta N p) U : ℂ) * S.diff N p 0 U := by
  rw [h.sub hc h.active le_rfl, Pi.sub_apply]
  rw [Solo.column, (hc.calibrated e N p h.active).encode, h.put U, (hc.wilson.starts N p).2]
  change weight C e N * _ * _ - _ = weight C e N * _ * (upper C S.row N p 0 U - _)
  rw [mul_sub]; rfl

private lemma pay (hp : S.Encoded N p) :
    (S.duet N p).cost N ≤ S.total (N,p)+(C.path.levels.params N).columns * (S.total (N,p) +
          (C.labels.level e).coeffSize ((S.duet N p).voice N).x) := by
  let L := C.labels.level e
  let x := (S.column N p N).x
  let y := (S.source N p N).x
  let p' := (C.path.levels.params N).columns
  have ha : 0 ≤ p' := zero_le_one.trans (C.path.levels.params _).columns_ge
  have ht : S.ticket N p N + L.coeffSize y ≤ S.total (N,p) := hp.afford
  have hu := cap_price (hp.cap N hp.active le_rfl)
  have hc : L.coeffSize (L.core x) ≤ S.total (N,p) + L.coeffSize (x-y) := by
    have hv := plus_coords L y (x-y)
    rw [add_sub_cancel ..] at hv
    exact (core_price _ _).trans (hv.trans (add_le_add_left ((le_add_of_nonneg_left hu).trans ht) _))
  change (S.duet N p).cost N ≤ _ + p' * (_ + L.coeffSize (x-y))
  rw [show (S.duet N p).cost N=p'*L.coeffSize (L.core x)+S.ticket N p N by simp [duet,primaryBill,x,p',L]]
  linarith only [ht, coeff_pos L y, mul_le_mul_of_nonneg_left hc ha]

private theorem push_minus (C : Family G) {X Y : Config G (C.side (m+1) p) → ℂ}
    (hX : Integrable X (prior G _)) (hY : Integrable Y (prior G _)) (β : ℝ) :
    let s := C.path.levels.clock.op m p
    s.push β (X-Y) = s.push β X - s.push β Y := by
  let H := C.path.levels.transition_mass m p β
  funext V
  simp only [Pi.sub_apply,StepData.push,smul_sub]
  exact integral_sub (StepData.push_slice H V X hX) (StepData.push_slice H V Y hY)

include hc h in
lemma Encoded.ships (i : ℕ) (hi : C.ref e ≤ i) (ht : i < N) :
    ((S.duet N p).voice i).density 0 (C.localSection e) (C.path.rep N p i) =
      ((C.S.block i).val : ℂ)^e • (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
        (((S.duet N p).voice (i+1)).density 0 (C.localSection e) (C.path.rep N p (i+1))) := by
  have he := hc.calibrated e N p h.active
  let H := C.path.rep N p (i+1)
  let X := (S.column N p (i+1)).density 0 (C.localSection e) H
  let Y := (S.source N p (i+1)).density 0 (C.localSection e) H
  have hb : C.ref e ≤ i+1 := hi.trans i.le_succ
  have hX : Integrable X (prior G _) := Source.TransferData.density_int hc.wilson he _ _ hb ht
  obtain ⟨hM,A,hA⟩ := Coefficient.envelope (C.localSection e) (hc.wilson.represents N p _ ht).good
    (h.cap (i+1) hb ht) (h.valid (i+1) hb ht)
  have hY : Integrable Y (prior G _) := Integrable.of_bound hM.aestronglyMeasurable A (Eventually.of_forall hA)
  -- expose BOTH zero anchors (not terms in Prop-based Format)
  change ((S.duet N p).voice i).density 0 _ _ = _ • (C.path.levels.clock.op i p).push _
      (((S.duet N p).voice (i+1)).density 0 _ _)
  rw [h.sub hc hi ht.le, h.sub hc hb ht, show (S.column N p i).density 0 _ _ =
    ((C.S.block i).val:ℂ)^e • (C.path.levels.clock.op i p).push _ X from he.unnormalized i hi ht _, h.step i hi ht]
  rw [push_minus C hX hY, smul_sub]

include hc h in
lemma Encoded.woke (hs : S.LocalBounds W N p) :
    (S.duet N p).Woke C.params W (C.localSection e) (S.total (N,p)) := by
  refine ⟨⟨h.active,le_rfl⟩,?_,?_, hs.one, h.ships hc,?_,pay h⟩
  · intro i hi ht
    have hp := h.both hc hi ht
    refine ⟨combo_format hp.1 (h.valid i hi ht),?_⟩
    rcases eq_or_lt_of_le ht with hN|hk
    · subst i
      have hw := combo_cap hp.1 (h.valid N hi ht) hp.2 (h.cap N hi ht)
      rw [show (S.duet N p).cost N=S.primaryBill N p N+S.ticket N p N by simp [duet]]
      exact hw
    rw [show (S.duet N p).cost i=S.deltaFee N p i by simp only [duet,if_neg hk.ne]]
    exact hs.income i hi hk
  · -- ancestor zero
    intro i hi ht
    let t := (C.path.levels.clock.op i p).ratio
    change 0 = t.parent 0
    have he := t.embed_parent 0; simpa only [show t.embed 0=0 from (t.root.map_zero)] using he.symm

  -- pairing
  change (S.column N p (C.ref e)).x - S.row (N,p) = 0
  rw [show (S.column N p (C.ref e)).x=_ from C.normalized hc h.active _, sub_self]

include hc h in
/-- Discounted estimate for genuine signed components *including unit*. -/
theorem Encoded.coins (hs : S.LocalBounds W N p) (hx : roomCost C.path.levels W) (hk : Bank W C.path.levels)
    (i : ℕ) (hr : C.ref e ≤ i) (ht : i ≤ N) :
    let P := S.duet N p
    P.cost i+(C.labels.level e).coeffSize (P.voice i).x ≤ escrow C N i (S.uniform (N,p)) := by
  have he := Work.G09.answer W C.path hx hk N p e (C.ref e) N _ _ _ (S.duet N p) _
    h.positive.le (h.woke hc hs) i hr ht
  dsimp only
  unfold escrow; apply (le_div_iff₀ (show 0 < gainChart _ _ _ from Real.exp_pos _)).mpr
  rw [mul_comm]; exact he

include hc h in
theorem Encoded.top_price (hs : S.LocalBounds W N p) (hx : roomCost C.path.levels W) (hk : Bank W C.path.levels) :
    (C.labels.level e).coeffSize (S.top (N,p)) ≤ S.uniform (N,p) + S.total (N,p) := by
  let L := C.labels.level e
  let P := S.duet N p
  let z := S.top (N,p)
  let x := (S.source N p N).x
  have he : L.coeffSize (P.voice N).x + L.coeffSize x ≤ S.uniform (N,p) + S.total (N,p) := by
    have ht : S.ticket N p N + L.coeffSize x ≤ S.total (N,p) := h.afford
    have hw := cap_price (h.cap N h.active le_rfl)
    have hv : 0 ≤ P.cost N := cap_price ((h.woke hc hs).origin N h.active le_rfl).2
    have hp : P.cost N + L.coeffSize (P.voice N).x ≤ S.uniform (N,p) := by
      simpa only [escrow, gainChart,sub_self,mul_zero,Real.exp_zero,div_one] using
        h.coins hc hs hx hk N h.active le_rfl
    linarith only [ht,hw,hv,hp]
  have ht := (plus_coords L (P.voice N).x x).trans he
  refine (le_of_eq ?_).trans ht
  change L.coeffSize z = _
  rw [show (P.voice N).x=z-x from congrArg (· - x) ((hc.calibrated e N p h.active).bare_coord _),sub_add_cancel]

variable (S : Solo C F e)



structure Priced (W : Worth) (f : Extraction.Order) : Prop where
  initial : Slow C f S.total
  every : ∀ᶠ i in f.fuse, S.Encoded i.1 i.2 ∧ S.LocalBounds W i.1 i.2

variable {S}

lemma uniform_slow (h : Slow C f S.total) : Slow C f S.uniform :=
  ((Slow.const (C:=C) (f:=f) (4:ℝ)).mul ((Slow.const (C:=C) (f:=f) (1:ℝ)).add (columns_slow (C:=C)))).mul h

lemma uniform_pos (h : S.Encoded N p) : 0 < S.uniform (N,p) := by
  unfold uniform
  have he := (C.path.levels.params N).columns_ge
  have hz := h.positive; dsimp; positivity

include hc in
/-- No cost assumption on the MATCH reference coordinates. Charge the
true terminal-inverse size. -/
theorem Priced.cost (p : S.Priced W f) (hx : roomCost C.path.levels W) (hk : Bank W C.path.levels) : dollar C f S.row := by
  rw [dollar_slow]
  apply ((uniform_slow p.initial).add p.initial).reduce
  filter_upwards [p.every] with i ⟨h,hs⟩
  exact (norm_cost _ (S.top i)).trans ((h.top_price hc hs hx hk).trans (Real.le_norm_self _))
end Solo
end YM.Push.RelayDifference
