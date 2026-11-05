import YM.MultiNext.VACUUM_STABILITY.Arrival.KWick
import YM.MultiNext.VACUUM_STABILITY.Arrival.Letters
import YM.Next.SCHEDULE.Support


set_option warningAsError false

/-!
# At the projected ROOT. Prices for intact analytic arrivals

One may expand into countably many variants with arbitrary (fixed-at-stage) polynomial
powers. Costs per all arrivals AFTER same vacuum setting, ALL allocations of that estimate
with true footage projection of the actual supports incl inspected final flag halo. Uniform
constant explicit at fixed pre-L res & L. Do not infer Estimate from the existence of a
vertex expansion in that class; the incoming priced caps on literals are from `Stability`.
Physical operation still needs to implement and honor variants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Arrival
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {V : Type} {n p : Side} {I J : Type}

-- receipt for one change in resolution with literal pre/post constants
structure Currency (G : Gauge) (n p : Side) where
  ratio : Ratio p n
  before : Survey G
  rates : Exchange
  smoothing : ℕ
  M : ℕ
  P : BudgetPoint
  /-- exponent available *in output support units* for ALL allocated variants -/
  strong : ℝ

namespace Currency
variable (A : Currency G n p)

structure Live : Prop where
  stays : ∃ (q : Quote) (i : ℕ), Buy A.before q A.rates A.smoothing i A.ratio.count.val
  works : foundation A.before A.rates A.smoothing ≤ A.P.supportExponent
  post : 0 ≤ A.strong
  okay : A.strong ≤ A.before.o.A A.smoothing + A.rates.extra
  ruler : 0 < A.M
  fits : A.P.B ≤ 2*A.M

def polyRoot (k : ℕ) (X : Support n) := Real.exp ((foundation A.before A.rates A.smoothing/4) * coverNumber A.P.B X) *
    ((coverNumber A.P.B X:ℝ)+1)^k

def scaleCost (k : ℕ) := footprintCost A.before A.smoothing A.rates k A.ratio.count.val A.M

def Renewal (i : Support n) (j : Support p) := Footage A.ratio A.rates.radius A.M i j




private lemma deviations (a : ℝ) (ha : 0 ≤ a) (M : ℕ)
    (B : I → Support p) (f : I→ℝ) (c : ℝ) (Y : Sigma (fun _i : I => J)→Support p) (hy : ∀ i,Y i ⊆ B i.1)
    (h : Ac.Hit B M f a c) (g : Sigma (fun _i : I => J)→ℝ) (hv : ∀ i : I,SumBudget (fun j => g ⟨i,j⟩) (f i)) :
    Ac.Hit Y M g a c := by
  intro x; refine Absolute.bundles (h x) fun i => ?_
  by_cases H : x∈B i
  · let u := Real.exp (a*coverNumber M (B i)); have hu : 0 ≤ u := (Real.exp_pos _).le
    simp only [if_pos H]; rw [mul_comm]; refine Absolute.compare (permit_mul (hv i) hu) (fun j => ?_) fun j => ?_
    · split; exact mul_nonneg ((hv i).1 j) (Real.exp_pos _).le; exact le_rfl
    split
    · rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ ((hv i).1 j)
      gcongr; exact Corona.cover_mono (hy ⟨i,j⟩) M
    exact mul_nonneg hu ((hv i).1 _)
  have he j : x∉Y ⟨i,j⟩ := fun hx => H (hy ⟨i,j⟩ hx)
  simp [H,he,SumBudget]
/-- What can be given to variant letters coming from each real input source (with localized
E/kicks, complete K packets) before even entering the component sums. -/
theorem activates (k : ℕ) (hA : A.Live) (X : I → Support n) (o : I→Site n) (ho : ∀ i,o i∈X i)
    (Y : Sigma (fun _i : I => J)→Support p) (hy : ∀ b,A.Renewal (X b.1) (Y b))
    {f : I → ℝ} {c e : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e) (hf : ∀ i,0 ≤ f i)
    (hg : Locations A.P X o f c) {g : Sigma (fun _i : I => J)→ℝ} (hV : ∀ i,SumBudget (fun j => g ⟨i,j⟩)
      (e*A.polyRoot k (X i)*f i)) : Ac.Hit Y A.M g A.strong (e*(A.scaleCost k*c)) := by
  obtain ⟨q,i,h⟩:=hA.stays
  let B j := halo (A.rates.radius*A.M) ((X j).image A.ratio.parent)
  let p' i := e*A.polyRoot k (X i)*f i
  apply deviations A.strong hA.post A.M B p' _ Y (fun _ => hy _) _ g hV
  intro x; have hF (j) : Footage _ _ _ _ (B j) := (show A.Renewal (X j) (B j) from fun _ ht => ht)
  have hU : ∀ x, SumBudget (fun i => if o i=x then Real.exp (A.P.supportExponent * coverNumber A.P.B (X i))*f i else 0) c := hg
  have hv := h.hit A.ratio _ _ hA.works hA.post hA.okay hA.ruler hA.fits X o ho B hF k f hf c hc hU x
  let φ (i : I) := Real.exp (A.strong*coverNumber A.M (B i))
  let ψ i := if x∈B i then Real.exp (A.strong * coverNumber A.M (B i) + (foundation A.before A.rates A.smoothing/4)*coverNumber A.P.B (X i))*
        ((coverNumber A.P.B (X i):ℝ)+1)^k * f i else 0
  have hw i : (if x∈B i then p' i*φ i else 0)=e*ψ i := by
    unfold ψ φ; split
    · rw [Real.exp_add]; unfold p' polyRoot; ring
    rw [mul_zero]
  have hz := permit_mul (show SumBudget ψ _ from hv) he
  change SumBudget (fun i => if x∈B i then p' i*φ i else 0) _
  simp_rw [hw]; exact hz
end Currency

namespace Flock
variable {F : Flock V G n} (A : Currency G n p) {Q : Rep G n} [Fintype V]

/-- Generic variant cost applicable at any of the physical supports. Distinguish:
 arrival kernels **paid** to these rates but not yet transported to output u/d. Includes E
 variations repeated as powers, and K variations with every vacuum history partner. -/
def Floats (X : I → Support n) (f : I→ℝ) (c : ℝ) : Prop := ∀ {J : Type}
    (Y : Sigma (fun _i : I => J)→Support p) (k : ℕ) (e : ℝ) (g : Sigma (fun _i : I => J) → ℝ),
    0 ≤ e → (∀ b, A.Renewal (X b.1) (Y b)) → (∀ i, SumBudget (fun j => g ⟨i,j⟩) (e*A.polyRoot k (X i)*f i)) →
    Ac.Hit Y A.M g A.strong (e*(A.scaleCost k*c))

namespace Attended
variable {o : V → Site p} {k : V → ℝ} {κ η : ℝ} {D : V → Pulse G n}

lemma crosses (hA : A.Live) (hQ : A.P=Q.p)
    (h : Attended F Q.p D (fun i => A.ratio.embed (o i)) k κ) {η : ℝ} {z : V→ℂ} (hh : 0 ≤ η) (hz : z∈allot o k η)
    (he : η ≤ 1) (hκ : 0 < κ) {σ c Λ δ b : ℝ} (H : Q.Lawful σ c Λ δ b) (hb : 0 ≤ b) :
    let o' (i : V) := A.ratio.embed (o i)
    (Floats (I:=Power V) A (pennyZone F) (raiseE F Q.p z) (Sugar.powerFee Q.p.order * η) ∧
      ∀ i : Power V, o' i.1.1∈pennyZone F i ∧ Q.p.Regular (pennyZone F i) (penny F i).ink ∧
        Q.p.supBounds (o' i.1.1) (pennyZone F i) ((penny F i).tell z) (raiseE F Q.p z i)) ∧
      ∃ f : Cases F → ℝ, Floats A (fun i => (owes F Q i).zone) f (b+κ*η) ∧
        ∀ i, 0 ≤ f i ∧ ∀ U, ‖(scrip F Q i).tell z U‖ ≤ f i := by
  intro o'
  have he' := extended o A.ratio hh hz
  obtain ⟨hv,hj⟩:=h.pepper z he' he; obtain ⟨f,x,hx,hF,-⟩:=hard_budget Q h H z he' hκ
  refine ⟨⟨?_,hj⟩,f,?_,fun i => (hx i).2⟩
  · intro J Y k e g he hy hg
    exact A.activates k hA _ _ (fun i => (hj i).1) Y hy (mul_nonneg (Sugar.power_pos _).le hh) he
      (fun i => (hj i).2.2.1) (hQ.symm ▸ hv) hg
  intro J Y k e g he hy hg
  exact A.activates k hA _ x (fun i => (hx i).1) Y hy (add_nonneg hb (mul_nonneg hκ.le hh)) he
    (fun i => (hx i).2.1) (hQ.symm ▸ hF) hg
end Attended
end Flock
end YM.Multi.Vacuum.Arrival
