import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Shawl
/-! # Amendment of Blaze.Silica.Clutch.stilly : book the logarithmic orbit piece itself
 Before scalar payoff, to allow clock changes. Needs enforce recurrent on this
 envelope; *raw* held U can be discontinuous outside. Purchase again explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open ConnectedActivityE6 Blaze Oriented Shell Channel Silica
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid
open Silica.Clutch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}

lemma apical (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p) (he : ∀ᶠ x in atTop,0≤p x) (hp : Rate G L (-(1/2)) q)
    {η rT T : ℝ} (Y : ℝ) (hr : Torch η rT T) : ∃ B : ℝ→ℝ, ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D → Works P L x S T' → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (y:E) (U : E→ Config G c) (F : Forest S.ratio)
      (X : Coat T' F) (β: ℝ) (u:E→ Directions G f) (w : Air f G) (z : E→ Air f G), X.x=x → X.χ=χ → X.width=K →
      Port P L η rT T Y X → Mode U y j (p x) → Clutch X w a β (q x) y j U u z →
        ∀ (Z:Stores S) (V:Config G f), (¬ (fun i=> X.enforce a (u i) (X.plaza (Z.dome (304*X.B))))=ᶠ[𝓝 y] fun _=>0) →
            Brush j (|B x| * Z.shares) 1 (fun i=> chalky (vary X (U i)) (u i) V Z + crispy (vary X (U i)) Z) y := by
  obtain ⟨A,hA,hT⟩:= hearthLift P L j h
  obtain ⟨Y',X,hY,hX,hv⟩:= Blaze.vines P L D hD K γ W χ j hr h he 1
  let p' x:= q x+2*a*Pressure.fiery G x L; let r x:= |p' x| +|Y' x|
  have hp': Rate G L (-(1/2)) p' := hp.add (Rate.flame.mul_left (2*a))
  have hζ {q : ℝ→ℝ} {k : ℝ} (h : Rate G L k q) := h.compare (v:=fun x=>|q x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  obtain ⟨H,hH,hO⟩:=cabinet P L D hD K γ W χ j h he (show Rate G L 0 r from ((hζ hp').add (hζ hY)).weaken (by norm_num))
  refine ⟨fun x=> (↑(Animals.ballCost (200*radiusB x+1))*Census.spots L*((|A x| + |H x|)+|H x|)),?_⟩
  filter_upwards [hT,hv,hO] with s hT hv hO c f S' T' hS hp hY E' _ _ _ y U F X' β u w z hs hχ hK hr h H' Z V' hx
  let I:=X'.plaza (Z.dome (304*radiusB s))
  have hhV : Port P L η rT T Y (vary X' (U y)) := by rw [H'.tipped]; exact hr
  have hx':I=X'.plaza (Z.dome (304*X'.B)) := by unfold I; rw [← hs]
  have hψ k (hk:k∈I) : ¬ (fun y=> X'.cone a (u y) k)=ᶠ[𝓝 y] fun _=>0 := fun h=> hx (h.mono (fun z hz=> prod_eq_zero (hx' ▸ hk) hz))
  have hΥ:= hO _ _ S' T' hS hp hY F X' hs hK hχ hr.placed
  have hV':= hΥ _ y U u H'.atV h
  let x y:= vary X' (U y); let g i:=voltage (x i)
  have hΓ i : Brush j (|Y' s|) 1 (fun y=>g y i) y := by
    have hu := hv c f S' T' hS hp hY F X' E' U y hs hK hχ h
    exact (hu hhV.placed hhV.sails.scale).1 i
  have hB' : X'.B = radiusB s := congrArg _ hs
  have he i (hi : i∈I) : Brush j (p' s) 1 (fun y=>u y i) y := by
    have hv := (H'.fostered i H'.pulse (hψ i hi)).2
    unfold Coat.t at hv; rw [hs,hp.length_eq] at hv; exact hv
  have hr (t) (q) (hq : q∈posted (turnStore t Z) (200*X'.B)) : Brush j (|A s| +|H s|) 1 (fun i=>rootface (x i) (u i) V' false t q) y ∧
      Brush j (|H s|) 1 (fun i=> Vine.costs (x i) (g i) t q) y := by
    let Y:= pull t 0 V'; let k:= choice t X'.k; let W i:=pull t 0 (U i)
    have hL:= hT _ _ S' T' hp E' Y k W y (Blaze.turn h t) q
    constructor
    · have hh : Brush j (|A s|) 1 (fun i=> loft T' X'.x Y k (W i) false q) y := by rw [hs]; exact hL.climb (le_abs_self _) le_rfl
      apply hh.separating
      apply (hV' q t ?_).climb (le_abs_self _) le_rfl
      intro i hi hf
      have hv : i ∈ I := by
        rw [hx']; apply mem_filter.mpr; refine ⟨mem_univ _,hf, Finset.not_disjoint_iff.mpr ⟨_,touch_extend ((rotates_dome ..).mp (mem_filter.mp hq).2) ?_,center_end i⟩⟩
        unfold distAt at hi; omega
      exact (he i hv).climb (((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))).trans (le_abs_self (r s))) le_rfl
    exact ((hΥ E' y U g H'.atV h q t (fun i _ _=> (hΓ i).climb ((le_add_of_nonneg_left (abs_nonneg _)).trans (le_abs_self (r s))) le_rfl))).climb (le_abs_self _) le_rfl
  apply (centralSum X' Z U u g V' hr (fun _=> rfl) (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)).climb _ le_rfl
  rw [abs_of_nonneg (by positivity : 0≤ ↑(Animals.ballCost (200*radiusB s+1)) * Census.spots L * ((|A s| + |H s|)+|H s|)), hp.length_eq, hB']; exact le_of_eq (by ring)
end YM.PhysicalNext.Repeat.Alabaster
