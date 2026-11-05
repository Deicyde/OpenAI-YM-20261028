import YM.Ovens.Coffee
import YM.Push.PRICE_COMPILER.Authors

/-!
# Fixed-L quantitative quotes for a stationary invocation

`Bid.Scene` is accepted WITH its premises. Need only the (L-dependent)
PriceGap in this price stack, take AFTER L but callable before Level/θ/w waits. Buy also the period test of Scene. Not proving such an estimate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG Wilson RG.Supply Precision Tree Exterior Bloch Laurent Pressure Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace

variable {G : Gauge} {p : Sheet G}

/-- include also F-calls. `shells` are counts in OUTPUT units,
here pay the whole macro cost there for simplicity (can afford even if
could pay in fine units). -/
def macroNeed (D : Rolls p) (j : ℕ) : ℕ := 2 + 100*((j+3)*(D.L j).val + 4*(D.L j).val)

lemma larger_paid {D : Rolls p} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}
    {a : Levels G} (he : macroNeed D ≤ W.shells) (ha : Paid I a) (m i : ℕ) : Larger (a.clock.op m i) (G:=G) := by
  have hx := (he _).trans (side_ge_shell ha m i)
  let S := a.clock.op m i
  have hh : 2 + 100 * macroR S.patch ≤ (a.S.side m i).val := by
    unfold macroR Patch.radius
    rw [show S.patch.J = a.clock.J (m+1) from rfl,
      show S.patch.L = D.L (a.clock.J (m+1)) from block_eq ha m]
    exact hx
  have hl : (a.S.side m i).val ≤ (a.S.side (m+1) i).val :=
    Nat.mul_le_mul_left _ (a.S.den_strict.monotone (Nat.le_succ _))
  refine ⟨(a.blocks m i).branches, ?_, ?_⟩
  · change 100 * macroR S.patch ≤ (a.S.side (m+1) i).val
    omega
  change 1 < (a.S.side m i).val
  omega

lemma priceGap_mono {c f : Side} {S : StepData c f} {k : Clip} {X : PathData G}
    {F : Forest S.ratio} {a b : ℝ} (h : PriceGap F k X a) (ha : b ≤ a) : PriceGap F k X b := by
  intro r v; exact (mul_le_mul_of_nonneg_right ha (by positivity)).trans (h r v)

/-- Gap & associated service priced at these numbers. -/
structure SceneRate (p : Sheet G) (D : Rolls p) (K : MapPrices) (g : ℕ → ℝ) : Prop where
  mono : Antitone g
  pos j : 0 < g j
  asks (j : ℕ) (c f : Side) (S : StepData c f) : S.kernel=p.kernel → S.patch.L=D.L j → S.patch.J=j →
      Larger (G:=G) S → ∀ (F : Forest S.ratio) (B C : Bed) (q r : Clip) (W : PathData G)
      (a b Λ u v w : ℝ) (T : Towers S.patch.L), Towers.Diagonal S B C T → Floor B q f (K.η j) u →
      W.Bounds q a b Λ → Attached B W → Sworn B f G → Floor C r c v w →
        PriceGap F q W (g j) ∧ ∃ ρ, Critical F q W ρ ∧ Guessed F (installed S.ratio T.A0) ρ ∧ HeatG F q W ρ C

theorem gap_prices (p : Sheet G) (D : Rolls p) (K : MapPrices) (u : ℕ → ℝ) (hu : ∀ j, 0 < u j) :
    ∃ g, g ≤ u ∧ SceneRate p D K g := by
  choose e he H using fun j : ℕ => (Integrated.stationary_scene (G:=G) (D.L j) j p.kernel (K.η j) (K.eta_pos j)).χ
  let v (j) := min (e j) (u j)
  refine ⟨rateLo v, fun j => (rateLo_le v j).trans (min_le_right ..), rateLo_anti _,
    rateLo_pos (fun i => lt_min (he i) (hu i)),?_⟩
  intro j c f S hk hr hs hh F B C p q X a b Λ u' v' w T hT ht hg hx hi hd
  obtain ⟨hb,hc⟩ := H j c f S hk hr hs hh F B C p q X a b Λ u' v' w T hT ht hg hx hi hd
  exact ⟨priceGap_mono hb ((rateLo_le v _).trans (min_le_left ..)), hc⟩

/-- Numerics ONLY. Quoted post-L, typically before β monitors. -/
structure AfterBill where
  error : ℕ → ℕ → ℝ -- absolute finite period error C_L
  decay : ℕ → ℕ → ℝ -- c_L (positive)
  forced : ℕ → ℕ → ℝ -- can use Move exponent at these rates, IF forced estimates earned
  err_pos j i : 0 < error j i
  dec_pos j i : 0 < decay j i
  snd_pos j i : 0 < forced j i

/-- Use it BEFORE fitting theta. -/
def AfterBill.post (q : AfterBill) (D : Rolls p) (gap : ℕ → ℝ) (h : ∀ i, 0 < gap i) : PostCost D where
  η := gap
  Γ := payHi (fromMax q.error)
  c := rateLo (fromMin q.decay)
  g := rateLo (fromMin q.forced)
  price := h
  pos := payHi_pos _
  posC := rateLo_pos fun _ => lt_min (q.dec_pos ..) (q.dec_pos ..)
  posG := rateLo_pos fun _ => lt_min (q.snd_pos ..) (q.snd_pos ..)



lemma AfterBill.paid (q : AfterBill) (D : Rolls p) (gap : ℕ → ℝ) (h : ∀ i, 0 < gap i) {j i : ℕ} (H : StepStages j i) :
    let t := q.post D gap h
    q.error j i ≤ t.Γ j ∧ t.c j ≤ q.decay j i ∧ t.g j ≤ q.forced j i :=
  ⟨(le_fromMax _ H).trans (le_payHi _ _), (rateLo_le _ _).trans (fromMin_le _ H),
    (rateLo_le _ _).trans (fromMin_le _ H)⟩




end YM.Push.PriceCompiler
