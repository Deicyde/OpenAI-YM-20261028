import YM.Extra.WILSON_STARTUP.Curve
import YM.Extra.WILSON_STARTUP.Funds

/-!
# RCake using the local top prescription

`Directed` is NOT constructed here. Needs compatibility *at every cutoff* of
B's bare unmasked paths with the top choice, Clip/cost/time conditions, and
that B's own extra tests first & retain actually accept the displayed output.
It is not enough to merely add predicate arguments with unverified truths.
No Move/advance assumption helps here. `tighten` allows requiring this exact
start again (e.g. later for sources) with no loss of unmarked start receipts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Start
open Filter Function RG Wilson Lattice Shoot Input Precision Bid Ovens Ovens.Pipes
open scoped Matrix.Norms.Frobenius Classical Topology
variable {G : Gauge} {n : Side}

def enumeration (G : Gauge) (n : Side) : ℕ ≃ Pellet (dictionary G n) :=
    Classical.choice (dictionary G n).encoding

def presentation (G : Gauge) (n : Side) (c : Clip) (b : BudgetPoint) :=
    cookie (payload c b G n) (enumeration G n) (Design.top G c) c b

theorem digests {c : Clip} {b : BudgetPoint} {l σ κ γ v β : ℝ} (hc : Decent c b)
    (ht : b.threshold ≤ threshold G b.order b.power)
    (hL : Loan b l σ κ γ) (hβ : l ≤ β) (hp : book G b ‖β‖ ≤ v) :
    (dictionary G n).Digests (payload c b G n β) b v (Real.exp γ-1) := by
  refine ⟨⟨regularFamily _,forcedFamily hc _,fun s x => moves ..,ink ht hc.direct le_rfl hp, hL.kernel hc hβ⟩,fun i U h => (h rfl).elim,
    ⟨fun _ => 0,summable_zero,fun i U => le_of_eq (norm_zero)⟩, fun i k U => rfl, fun i U V _ _ => rfl, fun i => measurable_const,?_⟩
  intro s x
  exact ⟨Padded.sends (reachAction s x),fun i => by
    change (Padded.name (Reach n) _).val = Finset.image _ (Padded.name (Reach n) _).val
    rw [Padded.name_sends]; exact supports_apply s x _, fun _ _ => rfl⟩

variable {S : Supply.Sheet G} {D : Supply.Rolls S} {T : Supply.Protection D} {W : Supply.Delays T} {Y : Supply.Bar W}
  {I : Supply.Wait Y} {O : ChartRatio G} {K : MapPrices} {Q : PostCost D}

abbrev layout (A : Levels G) (N p : ℕ) := presentation G (A.S.side N p) (A.params N).clip (A.budget N)

structure Allows (a : Levels G) (N : ℕ) : Prop where
  clip : Decent (a.params N).clip (a.budget N)
  radius : (a.budget N).threshold ≤ threshold G (a.params N).order (a.params N).power
  income : book G (a.budget N) (2*a.clock.hatBeta N) ≤ a.clock.allowance N
  receipt : ∃ σ κ γ, Loan (a.budget N) (a.clock.hatBeta N / 2) σ κ γ ∧
    quote κ (Real.exp γ-1) ≤ a.clock.forcedAllowance N

variable (B : Directed G I O K Q)

structure Approved (B : Directed G I O K Q) (N : ℕ) : Prop where
  paths : B.bake.path N N=Design.top G (B.a.params N).clip
  passes (p : ℕ) : ∀ β∈band B.a N,
    let u := layout B.a N p β
    B.bake.first N p u ∧ B.bake.retain N N p u

theorem oust (N p : ℕ) (h : Approved B N) (a : Allows B.a N) : Bid.Oust B N p := by
  let b := B.a.budget N
  let X := band B.a N
  let n := B.a.S.side N p
  let c := (B.a.params N).clip
  obtain ⟨σ,κ,γ,he,hh⟩ := a.receipt
  have ht : b.threshold ≤ threshold G b.order b.power := a.radius
  refine ⟨dictionary G n,payload c b G n,enumeration G n,?_⟩
  have hX (x) (hx : x∈X) : B.a.clock.hatBeta N/2 ≤ x := hx.1
  dsimp only
  change ((Curve b (Cake _ _ (B.bake.path N N) c b) X ∧ _ ∧ _) ∧ _)
  simp only [h.paths,topRatio]
  refine ⟨⟨curve ht a.clip.direct (fun x hx => he.slope.trans (hX x hx)),posed a.clip.direct (fun x hx => he.slope.trans (hX x hx)),he.little a.clip X hX⟩,fun x hx =>
    ⟨(h.passes p x hx).symm,κ,Real.exp γ-1,Real.exp γ-1, digests a.clip ht he (hX x hx) ?_,he.buys a.clip (hX x hx),hh,fun y => ?_⟩⟩
  · refine le_trans ?_ a.income
    unfold book overhead
    have h₁ := item_pos G b
    have ht : ‖x‖ ≤ 2*B.a.clock.hatBeta N := by rw [Real.norm_of_nonneg (he.slope.trans (hX x hx))]; exact hx.2
    gcongr
  simp only [payload,Pi.zero_apply,tsum_zero,Real.exp_zero,mul_one]; exact evaluates a.clip y



/-- Enforce same dictionary/presentation in future Stays histories, with no
new obligations for `Approved`. Keep all other parameters including paths,
branch kernel, chart, source/detector future scheduling on exactly this B.
-/
def tighten : Directed G I O K Q := { B with bake := { B.bake with first := fun N p u => B.bake.first N p u ∧ u = layout B.a N p u.beta } }

theorem approved_tight (N : ℕ) (h : Approved B N) : Approved (tighten B) N :=
  ⟨h.paths, fun p x hx => ⟨⟨(h.passes p x hx).1,rfl⟩,(h.passes p x hx).2⟩⟩

end YM.WilsonStartup.Start
