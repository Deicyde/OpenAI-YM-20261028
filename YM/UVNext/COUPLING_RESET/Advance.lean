import YM.Push.BETA_TRANSPORT.Margins
import YM.UVNext.COUPLING_RESET.Catalog
import YM.UVNext.COUPLING_RESET.Prices



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
`correct` calculates continuous actual Rep.beta and Rep.v, including the two
calibrating equalities, uniqueness on these trial templates (`scalars_unique`),
explicit correction bound relative to the *same Kin*, posterior inverse price
and label-norm continuity. For exact density equality globally and a Move see
the SEPARATE, physical `Remainder`. No proof here of the surplus hypotheses
on actual returns, let alone Remainder, selectivity of the two-configuration
signal under changing dictionaries, the existence of labelled estimates with
schedule-compatible costs or the creation of B or of a Wilson family. Use with
d fixed to have no effect on `terms` if a direct activity preparation (e.g.
by projection and analytic control as in E) can be used; otherwise allow a
slow dial-change in the additive reading, e.g. via `Template.motion`.

B.Move is band-free at output (indeed can't require the entire output to
stay in the next hatted band for inputs hitting edges!). Controls down the
calendar on SURVIVING intervals are treated separately.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Push.PriceCompiler Push.BetaTransport Lattice Wilson RG RG.Shoot RG.Supply Input Precision Filter Function Set
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}

abbrev width (a : Levels G) (m : ℕ) (q : ResetPrices) := q.radius (a.clock.J (m+1)) (a.clock.J m)
abbrev window (a : Levels G) (m : ℕ) (q : ResetPrices) := Icc (-width a m q) (width a m q)
abbrev funds (a : Levels G) (m : ℕ) (q : ResetPrices) := q.cost (a.clock.J (m+1)) (a.clock.J m) * a.clock.allowance m

abbrev In (a : Levels G) (m p : ℕ) := ℝ → Rep G (a.S.side (m+1) p)
abbrev Terms (a : Levels G) (m p : ℕ) := ℝ → ℝ → Activities G (a.S.side m p)

def target {a : Levels G} {m p : ℕ} (Q : In a m p) (x : ℝ) := (a.clock.op m p).push (Q x).beta (Q x).eval

variable (B : Directed G I Z K P) {N m p : ℕ}

def predictor (N : ℕ) {m p : ℕ} (Q : In B.a m p) (x : ℝ) := (Q x).beta+B.kin.alpha N m
def board (N : ℕ) {m p : ℕ} (F : Terms B.a m p) : Template G (B.a.S.side m p) :=
    ⟨B.bake.path N m,(B.a.params m).clip,B.a.budget m,F⟩

def Usable (η : ℕ → ℝ) (N m p : ℕ) (V : Config G (B.a.S.side m p)) :=
    let S := B.a.budget m
    flags S.threshold V = ∅ ∧
      sites (B.a.S.side m p) * (η (B.a.clock.J m)*S.threshold^2) ≤ kinetic (B.bake.path N m) (B.a.params m).clip S V

lemma usable {q : ResetPrices} {η : ℕ → ℝ} (h : PricedReset B.a η q) (hm : m ≤ N) (p : ℕ) : ∃ V, Usable B η N m p V := by
  have hw : 2 ∣ (B.a.S.side m p).val := dvd_trans (by decide : 2 ∣ 4) (B.a.S.side_four ..)
  have hD := B.support.cap N m hm
  rw [← B.bases] at hD
  exact (h m).1.2 _ hw _ _ _ _ hD

/-- Primitive input package on one actual template. In particular `surplus`
compares the REAL transferred vacuum at two all-good probes to all output
path channels including the loop read at the nonflat probe. It needs the
*committed* `alpha` with its sign. No input coefficient or bound from a
separate orbit of reselected thresholds, choices or arrays. Output labels
need not be β-independent but their dial-motion in this reading and their
regular cap must be cheap. The forced and regular representation postulates
inside Catalog are separate from scalar income. No `ShapeControl` needed just
to use the scalar service. Everything to be supplied in `Income` on actual
RG outputs is conditional, incl the availability of a suitable q with modest
growth/buyable before parameter continuation, and `pos` on all requested Q
(not taking such a sign bound from input `Lives.valid` for arbitrary bake). -/
structure Income (B : Directed G I Z K P) (N m p : ℕ) (q : ResetPrices) (s : Set ℝ) (Q : In B.a m p)
    (V : Config G (B.a.S.side m p)) (F : Terms B.a m p) : Prop where
  catalog : Catalog (board B N F) s (window B.a m q) (B.a.clock.allowance m) (B.a.clock.forcedAllowance m)
  pos : ∀ x∈s, 0 < target Q x 1 ∧ 0 < target Q x V
  surplus : ∀ x∈s, let A := board B N F
    |predictor B N Q x * A.leg V + A.background V - contrast (target Q) V x| ≤ sites (B.a.S.side m p) * funds B.a m q
  slow : ∀ x∈s, ∀ a∈window B.a m q, ∀ b∈window B.a m q,
    |(board B N F).add V x b - (board B N F).add V x a| ≤ sites (B.a.S.side m p) * funds B.a m q * |b-a|

/-- Extra genuine producer work necessary AFTER the scalar calculation. No
implication from localized two-test surplus to `shape` or to the expenditures
and additional recipe constraints here! In particular this cannot be priced
by applying the Teller theorem as if Plot were a partition. Estimate `shape`
really on sums/evaluator and all fields, including absolute support work at
the actual labels. Retain/next predicates in a real bake would be chosen for
unmarked and future uses, with independent producer proofs via the same data.
They can make use of the exact unnormalized evaluator identity and bought
scalar interval. Need NOT ask the output of an arbitrary such call is in the
band already, see `edge_obstruction`. -/
structure Remainder (B : Directed G I Z K P) (N m p : ℕ) (q : ResetPrices) (s : Set ℝ) (Q : In B.a m p)
    (V : Config G (B.a.S.side m p)) (F : Terms B.a m p) : Prop where
  shape : Template.ShapeControl (board B N F) s (window B.a m q) (target Q) V (predictor B N Q)
  forced : ∀ x∈s, ∀ a∈window B.a m q, (F x a).KBound (B.a.budget m)
    (Real.exp (-P.g (B.a.clock.J (m+1)) * B.a.clock.monitor (m+1)^2))
  recipe : ∀ x∈s, ∀ a∈window B.a m q, ∀ v, let T := (board B N F).trial (predictor B N Q) x a v
    T.eval = target Q x → B.bake.retain N m p T ∧ B.bake.next N m p T (Q x)

variable {B} {q : ResetPrices} {η : ℕ → ℝ} {s : Set ℝ} {V : Config G (B.a.S.side m p)}
    {F : Terms B.a m p} {Q : In B.a m p}

private lemma rate (h : PricedReset B.a η q) (hu : Usable B η N m p V) : let κ := (board B N F).leg V / 2
    0 < κ ∧ sites (B.a.S.side m p) * (funds B.a m q + B.a.clock.allowance m) ≤ κ * width B.a m q := by
  have hw := q.rad_pos (B.a.clock.J (m+1)) (B.a.clock.J m)
  obtain ⟨⟨hη,-⟩,ht⟩ := h m
  let z := η (B.a.clock.J m)*(B.a.budget m).threshold^2
  have hz : 0 < z := mul_pos hη (sq_pos_of_pos (B.a.budget m).threshold_pos)
  let n := B.a.S.side m p
  have hK : sites n * z ≤ (board B N F).leg V := hu.2
  have hh : 2*(funds B.a m q+B.a.clock.allowance m) ≤ z*width B.a m q := by unfold funds; dsimp [z,width]; linarith
  intro κ
  exact ⟨half_pos ((mul_pos (sites_pos n) hz).trans_le hK),by
    dsimp [κ]; nlinarith only [mul_le_mul_of_nonneg_left hh (sites_pos n).le,mul_le_mul_of_nonneg_right hK hw.le]⟩

lemma Income.paidResponse (h : PricedReset B.a η q) (hu : Usable B η N m p V) (he : Income B N m p q s Q V F)
    (hb : ContinuousOn (fun x => (Q x).beta) s) (ht : ContinuousOn (contrast (target Q) V) s) : let A := board B N F
    Response s (window B.a m q) (A.leg V / 2) (A.residual (target Q) V (predictor B N Q)) := by
  intro A
  have ⟨hμ,hκ⟩ := rate (F:=F) h hu
  apply A.response hμ (hb.add continuousOn_const) ht
  · intro x hx; exact he.catalog.along V continuousOn_const continuousOn_id (fun _ _ => hx) (fun _ hy => hy)
  · intro d hd; exact he.catalog.along V continuousOn_id continuousOn_const (fun _ hx => hx) (fun _ _ => hd)
  intro x hx a ha b hb hab
  have hn : 0 ≤ B.a.clock.allowance m := Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
  let n := B.a.S.side m p
  have hK : sites n * funds B.a m q ≤ A.leg V / 2 :=
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hn) (sites_pos n).le).trans <| hκ.trans
      (mul_le_of_le_one_right hμ.le (q.unit ..))
  have h₁ := neg_le_of_abs_le (he.slow x hx a ha b hb); rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h₁
  change _ ≤ A.add V x b - A.add V x a at h₁
  linarith only [h₁, mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr hab)]

lemma Income.balance (h : PricedReset B.a η q) (hu : Usable B η N m p V) (he : Income B N m p q s Q V F) {x : ℝ} (hx : x ∈ s) :
    let A := board B N F
    |A.residual (target Q) V (predictor B N Q) x 0| ≤ A.leg V / 2 * width B.a m q := by
  intro A
  have h₀ : 0 ∈ window B.a m q := abs_le.mp (by simpa using (q.rad_pos ..).le)
  have hc := he.catalog.valid x hx 0 h₀
  let n := B.a.S.side m p
  have hh : |A.add V x 0| ≤ sites n * B.a.clock.allowance m := volumeE _ hc V
  have hk := he.surplus x hx
  have hr := (rate (F:=F) h hu).2
  apply le_trans _ hr
  change |(predictor B N Q x + 0)*A.leg V + A.background V + A.add V x 0 - contrast (target Q) V x| ≤ sites n * _
  change |predictor B N Q x*A.leg V + A.background V - contrast (target Q) V x| ≤ sites n * _ at hk
  rw [add_zero]; have ⟨ha,hb⟩ := abs_le.mp hh; have ⟨hc,hd⟩ := abs_le.mp hk; exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Scalar service at one call, including a μ-posterior estimate and
continuous labelled rep, but without the other-output-field hypotheses.
Closed endpoints/ singleton s fine; solution values outside s unconstrained. -/
theorem correct (h : PricedReset B.a η q) (hu : Usable B η N m p V) (he : Income B N m p q s Q V F)
    (hq : Curve (B.a.budget (m+1)) Q s) (hx : ∀ x∈s, Lives B.bake N (m+1) p (Q x)) :
    ∃ d, let A := board B N F; let f := A.residual (target Q) V (predictor B N Q)
         let t := window B.a m q; let T := A.install (target Q) (predictor B N Q) d
         Response s t (A.leg V / 2) f ∧ Zeroes s t f d ∧ ContinuousOn d s ∧ Curve (B.a.budget m) T s ∧
           ∀ x∈s, (T x).eval 1 = target Q x 1 ∧ (T x).eval V = target Q x V := by
  have hc U : ContinuousOn (fun x => target Q x U) s :=
    ((lives_fixed hx).continuous_push _ (B.a.blocks ..).branches hq).comp
      (continuousOn_id.prodMk continuousOn_const) (f:=fun x => (x,U)) (fun _ h => ⟨h,mem_univ _⟩)
  let A := board B N F
  have hR := Income.paidResponse h hu he hq.beta (contrast_continuous he.pos (hc _) (hc _))
  obtain ⟨d,hz,hd⟩ := hR.balance_solve (q.rad_pos ..).le fun _ hx => Income.balance h hu he hx
  refine ⟨d,hR,hz,hd,?_,fun x hx => ?_⟩
  · have hs := he.catalog.stable (base:=predictor B N Q) (v:=scalar (target Q)) continuousOn_id hd (mapsTo_id s) hz.admissible
    exact ⟨(hq.beta.add continuousOn_const).add hd, ((hc 1).log fun x hx => (he.pos x hx).1.ne').div_const _,hs.reg,
      hs.forced,hs.continuous⟩
  exact A.passes hu.1 (he.catalog.valid x hx _ (hz.admissible hx)).regular.at_flat (he.pos x hx).1 (he.pos x hx).2 (hz.sol x hx)

lemma advance (h : PricedReset B.a η q) (hm : m < N) (hu : Usable B η N m p V) (he : Income B N m p q s Q V F)
    (hr : Remainder B N m p q s Q V F) (hq : Curve (B.a.budget (m+1)) Q s) (hx : ∀ x∈s, Lives B.bake N (m+1) p (Q x)) :
    ∃ d, let T := (board B N F).install (target Q) (predictor B N Q) d
         Curve (B.a.budget m) T s ∧ ∀ x∈s, B.Move N m p (T x) (Q x) ∧ |d x| ≤ width B.a m q := by
  obtain ⟨d,_,hz,_,hc,_⟩ := correct h hu he hq hx
  refine ⟨d,hc,fun x hx => ?_⟩
  have hw := hz.admissible hx
  have H := Template.realizes _ hr.shape hz hx (he.pos x hx).1
  have hW := hr.recipe x hx _ hw _ H
  have hD := B.support.cap N m hm.le
  rw [← B.bases] at hD
  refine ⟨⟨H,hW.2,⟨rfl,rfl,rfl,⟨hD,he.catalog.valid x hx _ hw⟩,hW.1⟩,hr.forced x hx _ hw,?_⟩,abs_le.mpr hw⟩
  change |(Q x).beta + B.kin.alpha N m + d x - (Q x).beta - B.kin.alpha N m| ≤ _
  rw [show (Q x).beta + B.kin.alpha N m + d x - (Q x).beta - B.kin.alpha N m = d x by ring]
  exact (abs_le.mpr hw).trans (q.unit ..)


end YM.UVNext.CouplingReset
