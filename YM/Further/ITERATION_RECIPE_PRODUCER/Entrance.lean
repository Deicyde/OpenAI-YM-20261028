import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WILSON_STARTUP.Copies
import YM.Further.ITERATION_RECIPE_PRODUCER.Oven
import YM.Progress.DIRECTED_RECIPE.Normalization


set_option warningAsError false

/-!
# At precisely this top, start translated and multi-marker calculations too

Evaluation and strengthened top `WILSON_STARTUP` receipts after the RAW
layout has been put on recipe's common-address dictionary (eligibility is
not the same field!). Check for availability of specific history APIs;
there's **no Histories.Shelf at all** after `finish`. Instead the actual
`Wide` theorem on our engine & the extra payments in Equip can launch
WilsonStartup.Mark and .Mixture. No multisource trajectory proof here,
nor paying all later required exponents e.g. those of `Extra.Multi`.
Uses `Family.Makes` only in the application to copy bills/smearing etc,
not to produce availability for a single-source `Heard` next.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Lattice Wilson RG RG.Supply RG.Shoot Precision Bid Pressure Exterior Extra.Iteration
open WilsonStartup Next.Scheduling Progress.DirectedRecipe Ovens Ovens.Pipes Input Extra.Histories
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

/-- The extraTest of **every** address in the final forced population,
including the reserved zeros, fails at the identity. Don't postulate Shelf
requests as an unverified hypothesis about this history. -/
lemma impossible {A : Activities G n} {b : BudgetPoint} (h : HasSlots b A) : ¬ Nonempty (Shelf A) := by
  rintro ⟨S⟩
  let t : StockTag n × ℕ := (⟨({0},{0}),Finset.singleton_nonempty _,Finset.Subset.refl _⟩,0)
  have he := S.check t (1:Config G n)
  rw [h.forced] at he
  obtain ⟨j,hj⟩ := ((folio G n) (S.name t)).property.1
  have hh := (he j hj).1
  rw [no_flags b.threshold_pos.le,Finset.inter_empty] at hh
  exact ((drawer G n).kernel j).inventory_ne.ne_empty hh.symm

lemma widened {A B : Activities G n} {P : BudgetPoint} {e k : ℕ ↪ ℕ} (h : Readdress P e k A B) {w : ℝ}
    {S : BudgetPoint} (he : S.threshold = P.threshold) (hg : A.KBound S w) : B.KBound S w := by
  have hS : Readdress S e k A B := { h with admits := fun i U => he.symm ▸ h.admits i U }
  exact hS.Kbound hg

variable {a : Levels G} {O : ChartRatio G} {M : Horizon a} {k : Kin M O} {r : Permissions a}
    {e : ℕ → ℕ → Exchange} {u : ℕ → ℕ → Postage} {N p : ℕ} {R : Rep G (a.S.side N p)}

lemma annual (h : PeriodFuture k e u (screen r) N p N R) (ht : Start.Allows a N) (he : Mixture.Extras a N) :
    WilsonStartup.Wide R ∧ R.activities.KBound (Start.expand (a.budget N)) (1/2) := by
  obtain ⟨hb,H,hx⟩ := begins_exact h
  let n := a.S.side N p
  have h' : Readdress (a.budget N) _ _ (Start.layout a N p R.beta).activities R.activities := Eq.mpr (congr_arg
    (fun R' => Readdress (a.budget N) _ _ (Start.layout a N p R.beta).activities (Rep.activities R')) hx)
    (H.ingredients.address (k.path N N) (a.params N).clip R.beta 0 (Start.enumeration G n))
  obtain ⟨σ,κ,γ,hy,hw⟩ := he.packets
  exact ⟨grows_wide h,widened h' rfl (Start.expandK ht.clip ht.radius hy hb.1 hw)⟩

open Source Cells Marker Mix Mixture
variable {C : Family G}

/-- `Mixture.terminal_ready` without assuming syntactic identity of the
cutoff `rep` with `Start.layout`. Otherwise same `Mixture` proof on the
selected Bolt's family and path at use; uses Wide and strengthened budget on Wilson top, not a
selected interacting OFF-trajectory assumption. -/
lemma inherits_mix (hC : C.Makes) {m i d : ℕ} (v : C.label d) (s : ℝ) {b : ℝ} (hv : ‖v‖ ≤ s) (hk : 1 ≤ b)
    (hr : C.ref d ≤ m) (hm : m ≤ i) (hN : i ≤ N) (h : ticket C b N p m i (hm.trans hN))
    (hw : WilsonStartup.Wide (C.path.rep N p N)) (hP : (C.path.rep N p N).activities.KBound (Start.expand (C.path.levels.budget N)) (1/2))
    (hd : Mark.Ready C.path.levels (C.localSection d) N) (he : Extras C.path.levels N)
    (hK : RefLi C.path C.labels C.localSection C.params C.ref) : Terminal C m N p (hm.trans hN) v (tide C s d N) := by
  let a := C.path.levels; let b' := a.budget N; let X := C.path.rep N p N
  let T := center C.S p (hm.trans hN) (0:Site (C.side N p)); let o := camp C p m N
  have hX := hC.wilson.represents N p N le_rfl
  obtain ⟨ha,hy,hb⟩ := h
  have h' := hr.trans (hm.trans hN)
  have hF : Far b' o := ⟨he.size,fun v q hv => by
    have he := hb N hN le_rfl v q hv
    have hi := le_mul_of_one_le_right (show 0≤ (b'.B:ℝ)^2 by positivity) hk
    exact_mod_cast hi.trans he⟩
  have hg : 0 < a.clock.hatCoupling N := inv_pos.mpr (Real.sqrt_pos.mpr (one_pos.trans (a.fits.delayed N)))
  have ht : a.clock.hatCoupling N ≤ b'.threshold := le_mul_of_one_le_right hg.le (Real.one_le_exp (sq_nonneg _))
  have hY := turned_fit C T hC h' hv
  have hz : DataCost (C.localSection d) o b' (turn C T v) (a.params N).columns (tide C s d N) :=
    fitted _ _ (a.params N).columns_ge hg ht he.overhead hY.1 hY.2 hd.widths (hK.loaded d N h')
  change X.activities.KBound (Start.expand b') (1/2) at hP
  rw [← show X.p = b' from hX.vac] at hz hP hF
  refine ⟨holds (hC.sections d) hX.good.labels.forced hz hF hP,fun s => continuous_integrable _ ?_,fun s => signal C T hC h' ha hd.widths hw _ s⟩
  unfold Overlay.Ride.Product; apply continuous_finsetProd
  intro j _; rw [funext (copies_eq (v:=v) C _ hC h' j 0)]; exact C.continuousO ..

end YM.Further.IterationRecipe
