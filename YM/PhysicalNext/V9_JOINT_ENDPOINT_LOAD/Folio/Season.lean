import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Primal
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Reading

/-! # Combined service & local cost receipt

Use `joint_calendar` with outlet/widths at funded settings. May NOT call on
an unrelated Directed witness without joint price compatibility. No field,
period, ancestry or tag used in those purchases. Left-order read locally
at partial sector is on the genuine kernel and one Chart and Y address when
the `Occupied` & `Orders` ports are actually implemented with the stipulated
mean continuation etc. Doesn't apply to all possible conditional rewriting
schemes, prove DCT for an interacting expansion, or buy the raised Offers
of other red tasks by Witness exchange. The exposure stake may also be zero
(if there are simply no distinct witnesses accounted). Choosing/compiling
a whole component family and proving other grouped multipliers' *per-site*
hit smallness and surviving-node rarity/compulsory savings from THEIR
physical contexts remains a substantial red task. Use these same weights
in both FHtree recursions, keep them multiplied by all activity bills, don't
price in more overlap systems with different support currency after the fact.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix Finset
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure Presented
open AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Reading Tariff
open MeasureTheory SectorNext.Remainder Push.AbsoluteSums
open Clockwork RG.Supply RG.Shoot Testing Push.PriceCompiler Input Next.Scheduling UVNext.PricedKernels
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u : Spot d} {Q : Booth} {t : Menu} {J : Aux}
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices} {V : Config G c} {Ω : Set (Config G c)} {P : Teller G} {h : Cafe}
    {H R ι α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype H] [Fintype R] [DecidableEq β] [DecidableEq γ]
    [DecidableEq H] [DecidableEq R] {X : Support c} {l : Viewport u X H R ι} {D₀ : u.Slices} {b : Finset ℕ} {q : Programme D₀ b} {z : q.Run α β γ}
    {a : Notice l} {B : Reading a z} {s : Seats l z} {M : Income α β γ (H⊕R)} {o : Site c} {j : ℕ}

structure Sweep (J : Aux) (P : Teller G) (h : Cafe) (Q : Booth) (t : Menu) (d : Desk G S) : Prop extends Scanned P h Q t d, Aux.Basis J Q.Q d P d.out.order

namespace Sweep
variable (hx : Sweep J P h Q t d) (hu : u=spectacle d A F κ)
include hx
omit [Fintype H] [Fintype R] [DecidableEq β] [DecidableEq γ] [DecidableEq H] [DecidableEq R] in
lemma offer (hj : max 1 M.plan ≤ j) : 1≤endow d Q.Q d.out.order j X M ∧ Escrow X M d Q.Q d.out.order j (endow d Q.Q d.out.order j X M) := by
  have he : Escrow X M d Q.Q d.out.order j _ := endows hx.day.limits.positive hj hx.reaches hx.day.beta hx.range hx.outlet.1 hx.outlet.2
  exact ⟨he.big,he⟩



include hu

end Sweep

section clock
variable {Z : ChartRatio G} {s : Sheet G} {K : MapPrices} {D : Rolls s} {Θ : Protection D}
    {C : ℕ→ℕ→Booth} {h : ℕ→ℕ→Cafe} {t : ℕ→ℕ→Menu} {w : ℕ→ℕ→ℝ} {W : Delays Θ} {Y : Bar W} {I : Wait Y} {a : Levels G}
    {P : Before}
private def Market (D : Rolls s) (K : MapPrices) (C : ℕ→ℕ→Booth) (Z : ChartRatio G) (h : ℕ→ℕ→Cafe) (t : ℕ→ℕ→Menu)
    (J : ℕ→ℕ→Aux) (j i : ℕ) (x : ℝ) := let P := Testing.query s K j i
    ∀ {c f : Side} (S : StepData c f), S.patch.L=D.L j → S.patch.J=j →
      ∀ d : Desk G S, Calling P Z (t j i).q P.below.power (h j i).r x d → Aux.Basis (J j i) (C j i).Q d P P.below.order

def Secured (C : ℕ→ℕ→Booth) (Z : ChartRatio G) (K : MapPrices) (h : ℕ→ℕ→Cafe) (t : ℕ→ℕ→Menu) (J : ℕ→ℕ→Aux) (V : Delays Θ) :=
  ∀ j x, V.betaEntry j ≤ x → ∀ i,Adj j i → s.first ≤ i → Market D K C Z h t J j i x

lemma season (J : ℕ→ℕ→Aux) (V : Delays Θ) : ∃ W : Delays Θ, OrderedDelays W ∧ DelayLe V W ∧ ∀ U, DelayLe W U → Secured C Z K h t J U := by
  have hp (j i : ℕ) : ∀ᶠ x : ℝ in atTop, Adj j i → s.first ≤ i → Market D K C Z h t J j i x := by
    by_cases hv : Adj j i ∧ s.first ≤ i
    swap; exact Eventually.of_forall fun _ a b=>False.elim (hv ⟨a,b⟩)
    let N:=Clockwork.patch D hv.1 hv.2
    let P := Testing.query s K j i
    filter_upwards [(J j i).purchased (C j i).Q P N Z (t j i).q (h j i).r P.below.power P.below.order] with x hx _ _ c f S hL hJ d he
    apply hx S d ?_ he
    cases hN : S.patch; rw [hN] at hL hJ
    congr
  have hr j : ∀ᶠ x in atTop, ∀ i, Adj j i → s.first ≤ i → Market D K C Z h t J j i x := by
    filter_upwards [hp j j, hp j (j-1)] with x hA hB i hv hI; rcases stepStages_target hv with hi|hi <;> subst i <;> first | exact hA hv hI | exact hB hv hI
  obtain ⟨U,hU,hV,he⟩ := delay_extra V _ (fun _ _ _=>True) hr (by simp)
  exact ⟨U,hV,hU,fun X hX => (he X hX).1⟩

lemma equipped {J : ℕ → ℕ → Aux} (hx : Secured C Z K h t J W) (hb : Funded Z K h C t w W) (hp : Paid I a) (m p : ℕ)
    (T : Tube G (a.clock.op m p)) (hQ : (Testing.query s K (a.clock.J (m+1)) (a.clock.J m)).Funds (a.clock.op m p) T)
    (u : Rep G (a.S.side (m+1) p)) (hu : u.beta∈band a (m+1)) :
    let j:=a.clock.J (m+1); let i:=a.clock.J m
    Sweep (J j i) (Testing.query s K j i) (h j i) (C j i) (t j i) (desk hb hp m p T u) := by
  intro j i
  let Q := Testing.query s K j i
  let S:=a.clock.op m p
  let d := desk hb hp m p T u
  have hl := hx j (a.clock.hatBeta m) (hp.pays m) i (step_paid a m) (first_le hp m) S
  have hh:=scanned hb hp m p T u hQ hu
  have hw := params_eq hp (m:=m)
  refine ⟨hh,?_⟩
  convert hl (block_eq hp m) rfl d (show Calling Q Z (t j i).q Q.below.power (h j i).r (a.clock.hatBeta m) d from ?_) using 1
  · change (a.params m).order = Q.below.order; exact congr_arg Stage.order hw
  convert hh.caller using 1 <;> first | rfl | skip
  exact congr_arg Stage.power hw.symm


end clock
end YM.PhysicalNext.JointLoad.Folio
