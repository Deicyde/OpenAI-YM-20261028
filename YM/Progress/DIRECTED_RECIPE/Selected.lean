import YM.Next.SCHEDULE.Calling
import YM.Progress.DIRECTED_RECIPE.Normalization
import YM.Progress.DIRECTED_RECIPE.Recipe

/-!
# Installed recipe: proving usability (pointwise part)

Performed step earns Lives and exact Move, with Path, strong K and actual
coupling reset preserved. Even ancestors are from the same numerical choices.
This doesn't *give* the pre-assembly expansion (all in `PeriodFuture` or
externally supplied to step), nor an availability result for each Curve yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Input Precision
open Next.Scheduling RG.Supply MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {a : Levels G} {M : Horizon a} {O : ChartRatio G}
    {k : Kin M O} {r : Permissions a} {e : ℕ → ℕ → Exchange} {F : ℕ → ℕ → Postage}
variable {s : Survey G} {q : Quote} {v : ℕ → ℕ} {K : MapPrices} {D : Rolls (s.paper q v)}
    {T : Protection D} {W : Delays T} {Z : Bar W} {I : Wait Z} {mould : Beam K D}
variable (paid : Paid I a) (tax : Regime mould e F W) (hk : k.Planned (mould.price F))

variable {N m p : ℕ} {U : Rep G (a.S.side m p)} {Q : Rep G (a.S.side (m+1) p)}
lemma begun {X d β} (H : SurfacePay k r N p β X d) (ho : β ∈ band a N) (e) (hk : k.Planned (mould.price F)) :
    Lives (recipe k e F r) N N p (fromTop k N p β X d) :=
  ⟨rfl,rfl,rfl,⟨hk.cap N N le_rfl,H.ingredients.gates ..⟩, PeriodFuture.begin ho H⟩

/-- The same prices for paths certified by `Kin.Planned`, the same prices as used
at every call through an Icc. No tightening of θ/allowance *after* acquiring
an output. Pasted strong K on Move. No order-reducing analysis fallback.
`period` implicit here is arbitrary. Including equality faces/masks. -/
lemma reload {X d Δ} (H : PeriodFuture k e F r N p (m+1) Q) (hQ : BatchPay k e F r N m p Q Δ X d)
    (hb : Q.beta ∈ band a (m+1)) (paid : Paid I a) (tax : Regime mould e F W) (hk : k.Planned (mould.price F)) :
    let u := receive k N m p Q Δ X d
    Lives (recipe k e F r) N m p u ∧
      u.activities.KBound u.p (Real.exp (-(mould.price F).g (a.clock.J (m+1)) * (a.clock.monitor (m+1))^2)) ∧
      |u.beta - Q.beta - k.alpha N m| ≤ 1 := by
  intro u
  have he : m<N := H.pockets.1
  have Hz : u.activities.Valid u.p (Echarge e F a m Q.beta) (Kcharge F a m Q.beta) :=
    hQ.ingredients.gates ..
  obtain ⟨hE,hK,hK',hb'⟩ := Deployment.recloses paid tax m p Q.beta hb u.activities Hz.boundE Hz.boundK
  have hp : u.activities.Valid u.p (a.clock.allowance m) (a.clock.forcedAllowance m) :=
    { Hz with boundE := hE, boundK := hK' }
  refine ⟨⟨rfl,rfl,rfl,⟨hk.cap N m he.le,hp⟩,PeriodFuture.struck he H hb hQ⟩,hK,?_⟩
  rw [show u.beta-Q.beta-k.alpha N m = Δ by change Q.beta+k.alpha N m+Δ-_-_=Δ; ring]
  exact hb' Δ hQ.bill

/-- Every admissible step input is a *real* rep in these respects.
At all configurations, even with flags. `Lives` does not pay the input band
on its own. Prices/horizon support are not assumed
sufficient for kernel analysis beyond those in `Planned`. -/
structure Packed (k : Kin M O) (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (r : Permissions a)
    (N m p : ℕ) (U : Rep G (a.S.side m p)) : Prop where
  lives : Lives (recipe k e F r) N m p U
  positive V : 0 < U.eval V
  gauge : GaugeInvariant U.eval
  signed z b V : U.eval (pull z b V) = U.eval V
  -- also valid for these very output densities, not just on bare cutoff.
  continuous : Continuous U.eval

section State
open Filter
lemma continuous_density {c f : Side} (S : StepData c f) (β : ℝ) (h : Config G f) :
    Continuous (S.density β h) := by
  unfold StepData.density; apply continuous_finsetSum
  intro i _
  have hg : Continuous fun V : Config G c => S.noise β (S.prediction h i) V := by
    change Continuous ((fun x : Config G c × Config G c => S.noise β x.1 x.2) ∘
      fun V : Config G c => (S.prediction h i,V))
    exact Continuous.comp (S.noise_cont β) (continuous_const.prodMk continuous_id)
  exact Continuous.const_mul hg (S.likelihood h i)

lemma continuous_push {c f : Side} (S : StepData c f) (β : ℝ) (L : S.patch.Branches S.kernel G)
    (A : Config G f → ℝ) (he : Integrable A (prior G f)) : Continuous (S.push β A) := by
  obtain ⟨C,hC⟩ := S.density_bound L β
  refine continuous_of_dominated (bound:=fun U => C * ‖A U‖)
    (fun V => (StepData.push_slice (S.isKernel L _) V A he).aestronglyMeasurable)
    (fun V => Eventually.of_forall (fun U => ?_)) (he.norm.const_mul C) ?_
  · rw [norm_smul, Real.norm_of_nonneg (density_strict S β L U V).le]
    exact mul_le_mul_of_nonneg_right (hC ..) (norm_nonneg _)
  refine Eventually.of_forall fun U => ?_
  exact (continuous_density S β U).smul continuous_const
end State

lemma Packed.env (h : Packed k e F r N m p U) : Envelope U.eval := U.envelope h.lives.valid

lemma Packed.continues (h : Packed k e F r N (m+1) p Q) :
    ∀ V, 0 < (a.clock.op m p).push Q.beta Q.eval V :=
  push_strict _ _ (a.blocks _ _).branches h.positive (h.env.integrable _)

lemma PeriodFuture.packed (H : PeriodFuture k e F r N p m U) (paid : Paid I a) (tax : Regime mould e F W)
    (hk : k.Planned (mould.price F)) : Packed k e F r N m p U := by
  induction H with
  | @begin β X d w h =>
    have ht := starter h w e F
    refine ⟨begun h w _ hk,?_,?_,?_,?_⟩ <;> rw [ht.raw]
    · exact bare_pos _
    · exact fun s U => bare_gauge ..
    · exact fun i s U => bare_pull ..
    exact bare_cont _
  | @struck m Q Δ X d hj hu hv hg ih =>
    have he := actual_eval hg (ih.continues 1)
    refine ⟨(reload hu hg hv paid tax hk).1,?_,?_,?_,?_⟩ <;> rw [he]
    · exact ih.continues
    · exact push_orbit _ (ih.env.integrable _) ih.gauge
    · exact fun s b => push_pull _ (ih.env.integrable _) s b (ih.signed s _)
    exact continuous_push _ _ (a.blocks m p).branches Q.eval (ih.env.integrable _)

/-- The real Move tickets, not just continuation constraints. -/
lemma attempts (H : PeriodFuture k e F r N p (m+1) Q) (hx : (recipe k e F r).next N m p U Q)
    (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) :
    (prepared k e F r paid hM hT hk).Move N m p U Q := by
  rcases (show m<N ∧ Q.beta ∈ band a (m+1) ∧ _ from hx) with ⟨hn,hb,Y⟩
  obtain ⟨Δ,X,d,hz,rfl⟩ := Y
  have he := H.packed paid tax hk
  obtain ⟨H1,H2,H3⟩ := reload H hz hb paid tax hk
  exact ⟨actual_eval hz (he.continues 1),hx,H1,H2,H3⟩

lemma firing {X Δ d} (hg : BatchPay k e F r N m p Q Δ X d) (hb : Q.beta ∈ band a (m+1))
    (H : PeriodFuture k e F r N p (m+1) Q) (paid : Paid I a) (tax : Regime mould e F W) (hM : M.Suffices K)
    (hT : LocalRatio O) (hk : k.Planned (mould.price F)) :
    let B := prepared k e F r paid hM hT hk
    B.Move N m p (receive k N m p Q Δ X d) Q :=
  attempts H ⟨H.pockets.1,hb,_,_,_,hg,rfl⟩ paid tax hM hT hk
end YM.Progress.DirectedRecipe
