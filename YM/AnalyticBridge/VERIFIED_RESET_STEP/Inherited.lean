import YM.AnalyticBridge.VERIFIED_RESET_STEP.Opening

/-!
Numerical /HRGv near-step compatibility. `rate/L` coefficient
and the extra +3 output support reserve must really be attainable together,
BEFORE any L (huge assumption in applications). The post-L term is bought
with committed theta. Do not impose arbitrary-after-L small `cost` in the
income port; `credit` lower floor there can be set pre-L (independent of
recoverable radius). Gates augment heights BEFORE realized I,a.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Time
open Filter Function Set Lattice Wilson RG Precision Collection Next.Scheduling Clock Instrument UVNext.CouplingReset Progress.DirectedRecipe
open Input Supply Push.PriceCompiler Shoot UVNext
open scoped Topology BigOperators Classical
variable {G : Gauge} {s : Sheet G} {D : Rolls s} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D}

abbrev PostList := ℕ → ℕ → Postage
abbrev RatioList := ℕ → ℕ → ℝ
def Pre (s : Sheet G) (f : RatioList) := ∀ j i, StepStages j i → 8*f j i ≤ credit G (s.profile i)*s.floorL j



def RawGate (Θ : Protection D) (f : RatioList) (J : PostList) (u : ℕ → ℕ → ℝ → ℝ) (j i : ℕ) (x : ℝ) :=
    let p := credit G (s.profile i); let L := ((D.L j).val:ℝ); let y := x + G.slopeConstant*Real.log L
    ∀ β, Next.Scheduling.inBand y β →
      (f j i / L + u j i x)*δE y + (J j i).residual plain (Θ.theta j) x y (gap β) ≤ p*δE x
lemma rawGate (Θ : Protection D) (hθ : ∀ j, Θ.theta j ≤ 1) {f : RatioList} (J : PostList) {u : ℕ → ℕ → ℝ → ℝ}
    (hf : Pre s f) (hu : ∀ j i,StepStages j i → Tendsto (u j i) atTop (𝓝 0)) (j i : ℕ) (hi : StepStages j i) :
    ∀ᶠ x : ℝ in atTop, RawGate Θ f J u j i x := by
  let L := (D.L j).val; let c := credit G (s.profile i); let A := G.slopeConstant * Real.log L
  have hp : 0<c := credit_pos ..
  have hL : 0 < (L:ℝ) := by unfold L; exact_mod_cast (D.L j).pos
  have h := mul_le_mul_of_nonneg_left (show (s.floorL j:ℝ) ≤ L by exact_mod_cast (D.large j).need) hp.le
  have he := (J j i).heat plain (Θ.theta j) (c/2) (hθ j) (by positivity)
  have hh : Similar δE := similar_gap_power _
  have hs := Clock.same
  filter_upwards [he,eventually_gt_atTop (1-A),just_near A,plain.support 2 one_lt_two, (hu j i hi).eventually (gt_mem_nhds (show 0<c/8 by positivity)),
    hh 2 one_lt_two] with x he hx hn hc hu hD
  let y := x + A
  intro β hβ
  have hy : 0 < y := by unfold y; linarith
  obtain ⟨hl,hr⟩ := band_gap y β hy hβ
  have hv := hc x y (hs x) hn
  have hhe := hv.gap
  obtain ⟨h1,h2⟩ := hhe
  have hC := (he y hn hv).2 (gap β) (by linarith) (by linarith)
  have hd := hD y x hn (hs x)
  have hL' : f j i / L ≤ c/8 := (div_le_iff₀ hL).mpr (by change (f j i) ≤ _; dsimp only [c,L] at *; linarith only [h, hf j i hi])
  have hz : 0 ≤ δE y := Real.rpow_nonneg (gp hy).le _
  change (f j i / L + u j i x)*δE y + _ ≤ c*δE x
  change (J j i).residual plain _ _ y (gap β) ≤ _ at hC
  change u j i x < c/8 at hu
  linarith only [hC,mul_le_mul_of_nonneg_right (add_le_add hL' hu.le) hz, mul_le_mul_of_nonneg_left hd hp.le]

def Inherited {Θ : Protection D} (W : Delays Θ) (f : RatioList) (J : PostList) (u : ℕ → ℕ → ℝ → ℝ) :=
    ∀ j x, W.betaEntry j ≤ x → ∀ i, StepStages j i → RawGate Θ f J u j i x

lemma buy (Θ : Protection D) (hθ : ∀ j, Θ.theta j ≤ 1) {f : RatioList} (J : PostList) {u : ℕ → ℕ → ℝ → ℝ}
    (hf : Pre s f) (hu : ∀ j i,StepStages j i → Tendsto (u j i) atTop (𝓝 0)) (V : Delays Θ) :
    ∃ U : Delays Θ, Boost V U ∧ ∀ W : Delays Θ, Boost U W → Inherited W f J u := by
  obtain ⟨m,-,he,hm⟩ := collect_upper V.betaEntry (fun j x => ∀ i,StepStages j i → RawGate Θ f J u j i x) fun j =>
    eventually_transitions j _ _ (rawGate Θ hθ J hf hu j)
  exact ⟨{V with betaEntry := m},⟨he,le_rfl,le_rfl,le_rfl⟩,fun W H j x hx => hm j x ((H.beta j).trans hx)⟩

/-- Extension for downstream pricing (sector pressure/Cosmos bills not
purchased here). Sufficient criterion for the *raw* prices, at the correct
beta cut even if a stage is repeated. Reset radius can be quoted post-L;
it is the **cost** which must permit an early coefficient error at least
4*credit, and the Move rate exponent must likewise leave the stated share
(compare `Machine.coverage`). D and θ never reissued; callers finish buying
W and then issue a single wait (no claim of crediting an existing I). -/
theorem beforeWait (g : G.Simple) : ∃ η, Sensors s η ∧ ∀ (D : Rolls s) (Θ : Protection D) (q : ResetPrices)
    (f : RatioList) (F J : PostList) (P : PostCost D) (A : Scouts (F:=F)) (u : ℕ → ℕ → ℝ → ℝ), (∀ j, Θ.theta j ≤ 1) → Pre s f →
    (∀ j i,StepStages j i → Tendsto (u j i) atTop (𝓝 0)) → ∀ V : Delays Θ, ∃ U : Delays Θ, Boost V U ∧ ∀ W : Delays Θ, Boost U W →
      Opened W P A ∧ Inherited W f J u ∧ (∀ j x, W.betaEntry j ≤ x → ∀ i,StepStages j i → CubicGate D q j i x) ∧
      ∀ Y : Bar W,∀ I : Wait Y,∀ a : Levels G,Paid I a → PricedReset a η q := by
  obtain ⟨η,hη⟩ := sensors g s
  refine ⟨η,hη,fun D Θ q f F J P A u hθ hf hu V => ?_⟩
  obtain ⟨X,hX,hS⟩ := buy Θ hθ J hf hu V
  obtain ⟨Y,hY,hM⟩ := open_shop g P A X
  obtain ⟨c,-,hc,hC⟩ := delay_cubic D q Y.betaEntry
  obtain ⟨b,-,hb,hB⟩ := can_delay_reset q η (fun i => (hη i).1) c
  let Q : Delays Θ := {Y with betaEntry := b}
  have hQ : Boost Y Q := ⟨hc.trans hb,le_rfl,le_rfl,le_rfl⟩
  exact ⟨Q,hX.chain (hY.chain hQ),fun W H => ⟨hM W (hQ.chain H),hS W (hY.chain (hQ.chain H)),fun j x hx => hC j x ((hb j).trans ((H.beta j).trans hx)),
    fun _ _ a h => buys_reset a h hη fun j x hx => hB j x ((H.beta j).trans hx)⟩⟩




end YM.AnalyticBridge.VerifiedReset.Time
