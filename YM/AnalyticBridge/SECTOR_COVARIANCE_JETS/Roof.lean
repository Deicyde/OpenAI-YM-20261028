import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Coloring
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sky

set_option warningAsError false

/-! E counting presentation compatible with actual SectorChange, under
same test branches as needed for exponential jet application. Keep
prices and years separated even if produced together. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Completion FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C x η b g : ℝ}

/-- Data additionally about *completed* A, common-radius E pane price.
No padding factor backed into any measure. Includes purpose-specific
ordered rate (for next logdet etc.). On coherent sector witnesses the
completion agrees with the *chosen* actual prescription. -/
def Deck (G : Gauge) (p : Teller G) (P : Patch) (x C r : ℝ) (k : ℕ) (σ b η g : ℝ) :=
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → p.Funds S T →
      100*(1+radiusB x) ≤ c.val → ∀ (V : Config G c) (t:S.Choices) (A : Stores S) (F : Forest S.ratio),
        A.flags=RG.flags (temp x) V → ∀ B : Directions G c, ‖B‖ ≤ r →
          let Q := painted T A F t x V; let W := allPanels A F (G:=G) (x:=x); let o := start A F (G:=G) (x:=x)
          RatesPaid o o σ C k Q B ∧ Gapped (Q B) η ∧ (Q B).PosDef ∧
            Installed o Q W B σ (rate (-b) (radiusB x)) C g k ∧
              obscure W Q =ᶠ[𝓝 B] paint (prism T A F t x V) 1

lemma Sky.contract (P : Patch) (p : Teller G) {u : ℝ} (ht : u ≤ r) (h : Sky G p P x C r k σ b η g) :
    Sky G p P x C u k σ b η g :=
  ⟨h.growth,@fun _ _ S T he hx hy V t A F hV B hh => h.branch S T he hx hy V t A F hV B (hh.trans ht),
    @fun _ _ S T he hx hy V t A F hV B hh => h.shade S T he hx hy V t A F hV B (hh.trans ht)⟩

/-- Also carry exact equality of Fog and completed C up to unused slot completion on a germ. -/
theorem coverall (P : Patch) (G : Gauge) (p : Teller G) (hb : P.Branches p.bind G) (k : ℕ) :
    ∃ r : ℝ, 0 < r ∧
    ∃ (C M σ d b t η ε g v : ℝ), 0<C ∧ 0<M ∧ 0<σ ∧ 0<d ∧ 0<b ∧ 0<t ∧ 0<η ∧ 0<ε ∧ 0<g ∧ 0<v ∧
    ∀ᶠ x : ℝ in atTop, Sky G p P x C r k σ b η g ∧ Deck G p P x M r k d t ε v := by
  obtain ⟨C,r,σ,b,η,g,hc,hr,hσ,hb,hη,hg,h⟩ := fromTeller P G p hb k
  let ε := min η 1; let K:=max 1 C
  have he : 0<ε := lt_min hη zero_lt_one
  obtain ⟨M,d,t,v,hm,hK,hd,hu,ht,hv,H⟩ := aperture P G hσ (hc.le.trans (le_max_right 1 C)) he k
  refine ⟨r/2,half_pos hr,C,M,σ,d,b,t,η,ε,g,v,hc,hm,hσ,hd,hb,ht,hη,he,hg,hv,?_⟩
  filter_upwards [h,H] with x hx hL
  refine ⟨Sky.contract P p (half_le_self hr.le) hx,?_⟩
  intro c f S T hP hT he' V t A F hV B hB Q W o
  have hp : ‖B‖ < r := hB.trans_lt (half_lt_self hr)
  have hf (a : Directions G c) (hp : ‖a‖ ≤ r) := hx.branch S T hP hT he' V t A F hV a hp
  let A' := pilot T A F t x V
  have h1 : RatesPaid o o σ K k Q B := blank_pay (p:=o) (by rw [show o ∘ Sum.inl = front A F from rfl]; exact (hf B hp.le).2.1)
  have ht' : (A' B).IsSymm := by unfold A'; rw [pilot_eq]; unfold Matrix.IsSymm; rw [transpose_mul,transpose_transpose]
  have hy : Gapped (Q B) ε := (wide_gap ht' ((hf B hp.le).2.2.1)).2
  have hw := even_painted T A F t x V
  refine ⟨reducePay h1 hu hK le_rfl, hy, dissolves hy (hw B) he, hL.2 o Q W B ?_ hw h1 hy (reachLayers A F hL.1),?_⟩
  · intro u hu; rw [← hP]; exact whole_start A F x u hu
  filter_upwards [continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds hp)] with y hy
  have hχ := stocked A F x T t (increment V y) hη (show Gapped (A' y) η from (hf y hy.le).2.2.1) hL.1
  exact hχ.2.1


end YM.AnalyticBridge.Covariance
