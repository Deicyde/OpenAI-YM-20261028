import YM.WilsonBulk.Agenda.Hat

/-!
# Calendar.LAND sufficient sizing. Uses ANY prior A.& Levels meeting numerical goals; heater follows at all N.

Strengthens quota E≤J (fixed smoothing J supporting height vertices). h k geometry requirements still stipulated per cases; no claim about lower E totals computed on Mesh beyond cone, except exact analytic formulas at every N. Does not do diagonal or Gaussian continuum derivative interchange.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet.Agenda
open Function Filter Lattice Laurent RG Schedule Finset Precision Exterior Stationary Audience Recall Pert.Bulk Sheet Atelier Bloch Work.F08 Supply
open scoped Topology Classical ENNReal BigOperators
variable {G : Gauge} {A : Levels G} {H : Horizon A} {F : MapPrices} {i j k n m ℓ N N' E : ℕ} {x a b p σ θ μ w C t δ : ℝ} {L : Side} {P : Patch}
variable {K : KernelChoices} {J : ChartRatio G} {S : Lit G A.clock.kernel F} {M : Motions A}
-- numeric only. Lens constants postBlock judged *solely* at local β shadow. Delays choose at each J to buy. Protect for all horizons within.
structure Arena (F : MapPrices) (S : Lit G A.clock.kernel F) (a : ℝ) (J : ChartRatio G) : Prop where
 list (i : ℕ) (e : ℕ) : e ≤ stage A (i+1) → Threshold S a (stage A i) (stage A (i+1)) (A.S.block i) e
 fat (i : ℕ) : Real.exp 1 ≤ A.clock.hatBeta i
 polite (i : ℕ) (T : historyModel A i) (e : ℕ) : e ≤ stage A (i+1) → postTranche S T J (stage A i) e a ≤ zAge A i

abbrev Upon (A : Levels G) (E ℓ : ℕ) := max E 5 ≤ stage A (ℓ+1)
lemma upon_mono (he : Upon A E ℓ) (hi : ℓ ≤ i) : Upon A E i:= he.trans (A.fits.mono (by omega : ℓ+1 ≤ i+1))
lemma upon_prepared (A : Levels G) (e : ℕ) : ∀ᶠ i in atTop,Upon A e i := (A.fits.deep.eventually_ge_atTop _).mono (fun i hi=>hi.trans (A.fits.mono (show i ≤ i+1 by omega)))
namespace Arena
variable (hG : G.Simple) (T : Arena F S a M.j)
include hG T
lemma use (he : Upon A E ℓ) (hp : zAge A k ≤ x) : Develop S M ℓ k E x a (1+G.slopeConstant) 1 := by
  have hv i (hi: ℓ ≤ i) : E ≤ stage A (i+1):= (le_max_left ..).trans (upon_mono he hi)
  exact ⟨fun i hi=>⟨(le_max_right ..).trans (upon_mono he hi), T.list i E (hv i hi)⟩, (ages_one (T.fat k)).trans hp, fun i hi=> (T.polite i (M.tree i) E (hv i hi)).trans (age_charge A hG T.fat i k hp)⟩
end Arena

-- calendar purchase, no Θ.Sufficient later. K & penalty given; Delays monotone additional. Provide simple for "ClockExtension Contract: preSteps all e≤j; postSteps all S,Dr ready". Proof quantifies over all `A.clock.kernel= K` including actual levels from chosen Family. Can assemble with arbitrary granted etc. Need no τ monotonic for support. Export for integrating choices.

abbrev Prelit (S : Lit G K F) (a : ℝ) (τ : ℕ→ℕ) := ∀ i j (P:Patch), P.J=j → Agenda.after i j → τ j ≤ P.L.val → ∀ E≤j,Threshold S a i j P.L E
lemma Prelit.enlarge {τ v : ℕ→ℕ} {S : Lit G K F} (h : Prelit S a τ) (hv : τ ≤ v) : Prelit S a v := fun i j p hp ht hh=> h i j p hp ht ((hv j).trans hh)
lemma invoice {v : ℕ→ℝ} {τ : ℕ→ℕ} {L : ℕ→ Side} (hD : Dawn J a S L v) (ht : Prelit S a τ)
     (hL : ∀ i,(τ i) ≤ (L i).val) (hs : A.clock.factor=L) (hp : ∀ i:ℕ, v (stage A (i+1)) ≤ A.clock.hatBeta i) : Arena F S a J := by
  have hf (i : ℕ) : (historyPatch A i).L= L (stage A (i+1)) := (hs ▸ (A.fits.sameFactor i)).symm
  exact ⟨fun i e hv=> ht (stage A i) (stage A (i+1)) (historyPatch A i) rfl (axle A i) (hf i|>.symm ▸ hL _) _ hv,
    fun i=>(hD.strong _).trans (hp i), fun i V e he=> hD.peak (stage A i) (stage A (i+1)) (historyPatch A i) V (axle A i) rfl (hf i) e he _ (hp i)⟩

/-! Reader note casting along `A.clock.kernel = K` is intentional. The existence theorem chooses one `S : Lit` BEFORE issuing length or `K'`, not each realized level. To carry all cone computations without roleT period p. The parameters `Will` and `Rolls` of actual Grantor need only pay these requests; if not, do not apply invoice. Consumer: uniform all T & κ adjust expansions. -/
lemma renounce (K : KernelChoices) (G : Gauge) (J : ChartRatio G) (F : MapPrices) (a : ℝ) (h : a<1) : ∃ S : Lit G K F,∃ τ:ℕ→ℕ, Prelit S a τ ∧
     ∀ L : ℕ→Side, (∀ i, τ i ≤ (L i).val) → ∃ v:ℕ→ℝ,Dawn J a S L v ∧
       ∀ (A : Levels G) (he : A.clock.kernel=K), A.clock.factor=L → (∀ i:ℕ,v (stage A (i+1)) ≤ A.clock.hatBeta i) → Arena F (he.symm ▸ S) a J := by
  obtain ⟨S⟩:= Lit.exists G K F; obtain ⟨τ,hτ⟩:= S.allGates a h; refine ⟨S,τ,hτ,fun L hL=>?_⟩; obtain ⟨v,hv⟩:= allPost J S a L; refine ⟨v,hv,fun A he P H=>?_⟩; subst K; exact invoice hv hτ hL P H

/-- Pinned default reference setting (E,H finite; projection c-k). Reader with `ν` objective, pre widths.
    use via common C wrapped A. Strength of residual at all actual κ fixed. -/
def gentleFund (G : Gauge) (a b : ℝ) (h : G.Simple) (ha : a<1) (hb:b < a) (hp:0 < b) : Fund := ⟨a,b,1+G.slopeConstant,1,ha,hb,hp,add_nonneg zero_le_one (Gauge.slopeConstant_pos h).le⟩
lemma oracle (hF : Arena F S a M.j) (hG : G.Simple) (hf : H.Suffices F) (hk : LocalRatio M.j)
    (ha : a<1) (hb:b<a) (hp : 0<b) (e : ℕ) :
    let P:= Fund.publicity H S M hf hk (gentleFund G a b hG ha hb hp) e
    (∃ p,Tariff p ∧ ∀ k ≤ e, ∀ n,P.Ledger p k n) ∧
     ∀ ℓ k, Upon A e ℓ → ∀ x≥zAge A k,P.Land ℓ k x := by
  intro Y; exact ⟨Y.budgetAll hG, fun ℓ k h y hy=> Fund.developed _ hf hk (hF.use hG h hy)⟩
end YM.WilsonBulk.Parapet.Agenda
