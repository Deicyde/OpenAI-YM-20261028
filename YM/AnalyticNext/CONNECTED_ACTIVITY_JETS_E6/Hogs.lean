import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Clods
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Intrados
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sortie

/-!
# Difference from reference expenditure across footprint W

 With arbitrary held-U basis, pay ONLY when chart masks persist.
 Powers with count ok if absorbed over shares; β-exp uptake STILL needs
 value charge, no differentiating log-j near J zero required. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] {x : E}
variable {a A α β γ d η σ W s b μ r Q p q v : ℝ} {j n : ℕ}
variable {V : E→ Config G c} {w : E → Directions G f} {u : E→ Air f G}
lemma stilly (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W a : ℝ) (χ : Chi) (j : ℕ)
    {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) {p q : ℝ→ℝ} (h : Rate G L (-(1/2)) p) (he : ∀ᶠ x in atTop,0≤p x) (hp : Rate G L (-(1/2)) q)
    {η rT T : ℝ} (Y : ℝ) (hr : Torch η rT T) : ∃ B, Rate G L 1 B ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S:StepData c f) (T':Tube G S), S.patch=D → Works P L x S T' → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (y:E) (U : E→ Config G c) (F : Forest S.ratio)
      (X : Coat T' F) (A : Rep G f) (u:E→ Directions G f) (w : Air f G) (z : E→ Air f G), X.x=x → X.χ=χ → X.width=K →
      Port P L η rT T Y X → Mode U y j (p x) → Intake P T' x A → Clutch X w a A.beta (q x) y j U u z →
        ∀ (Z:Stores S) (V:Config G f), (¬ (fun i=> X.enforce a (u i) (X.plaza (Z.dome (304*X.B))))=ᶠ[𝓝 y] fun _=>0) →
        let f i:= plumeLog (vary X (U i)) a A Ñ (u i) V Z
        Brush j (|B x| * Z.shares) 1 (fun i=> f i - f y) y := by
  obtain ⟨A,hA,hT⟩:= hearthLift P L j h
  obtain ⟨B,V,hB,hΞ,hP⟩:= mistropy P L D hD j Y hr h
  obtain ⟨E,hE,hG⟩:= puffs G L χ a hÑ hp j
  obtain ⟨Y',X,hY,hX,hv⟩:= Blaze.vines P L D hD K γ W χ j hr h he 1
  let p' x:= q x+2*a*Pressure.fiery G x L; let r x:= |p' x| +|Y' x|
  have hp': Rate G L (-(1/2)) p' := hp.add (Rate.flame.mul_left (2*a))
  have hζ {q : ℝ→ℝ} {k : ℝ} (h : Rate G L k q) := h.compare (v:=fun x=>|q x|) (Eventually.of_forall fun x=> (abs_abs _).le)
  obtain ⟨H,hH,hO⟩:=cabinet P L D hD K γ W χ j h he (show Rate G L 0 r from ((hζ hp').add (hζ hY)).weaken (by norm_num))
  let D' x:= (2*betaF G x L)*(↑(Animals.ballCost (200*radiusB x+1))*Census.spots L*((|A x| + |H x|)+|H x|))
  let S x:= D' x+((Animals.ballCost (200*radiusB x+2):ℝ)*Itinerary.density L* |B x|)+((Animals.ballCost (304*radiusB x+2):ℝ)*Itinerary.density L* |E x|)
  have hd : Rate G L 1 D' := by
    convert ((Rate.hat.mul_left 2).mul (((width_rate G L 200 1).mul_right _).mul (((hζ hA).add (hζ hH)).add (hζ hH)))) using 1; ring
  have hs : Rate G L 1 S := by
    have hF (s l : ℕ) (u) (h : Rate G L 0 u) : Rate G L 1 (fun x=> (Animals.ballCost (s*radiusB x+l):ℝ)*Itinerary.density L*u x) :=
      (((width_rate G L s l).mul_right _).mul h).weaken (by norm_num)
    exact (hd.add (hF _ _ _ (hζ hB))).add (hF _ _ _ ((hζ hE).weaken (by norm_num)))
  refine ⟨fun x=> S x+ S x,hs.add hs,?_⟩
  filter_upwards [hT,hP,hG,hv,hO] with s hT hP hG hv hO c f S' T' hS hp hY E' _ _ _ y U F X' R u w z hs hχ hK hr h hr' H' Z V' hx f'
  let X:=X'; let I:=X.plaza (Z.dome (304*radiusB s))
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
  have hC i (hi : i∈visit Z (200*X'.B)) : Brush j (|B s|) 1 (fun y=> (x y).condensation i) y :=
    ((hP _ _ S' T' F X' E' U y hS hp.length_eq hs hhV h i).1).climb (le_abs_self _) le_rfl
  have hg i (hi : i∈I) : Brush j (|E s|) 1 (fun y=> X'.gentry Ñ a (u y) i) y := hG _ _ S' T' F X' hs hp.length_eq hχ E' w R.beta y U u z H' i
  let e i := ∑ j∈visit Z (200*X'.B), (x i).condensation j; let a i:= ∑ j∈I,X'.gentry Ñ a (u i) j
  have hj : I.card ≤ Z.shares*Animals.ballCost (304*radiusB s+2)*Itinerary.density L := by
    dsimp only [I]; rw [← hp.length_eq]; exact (card_le_card (show X.plaza _⊆visit Z (304*radiusB s) from
      fun i hi=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2.2⟩)).trans (touch_price S' _ _)
  have hI : (visit Z (200*X'.B)).card≤ Z.shares*Animals.ballCost (200*radiusB s+2)*Itinerary.density L := by rw [hB', ← hp.length_eq]; exact touch_price S' _ _
  have hh (O : Finset (Bond f)) (C : ℕ) (hC:O.card≤C) (q : ℝ) (A : E'→Bond f→ℝ) (he:∀ i∈O,Brush j (|q|) 1 (fun x=>A x i) y) :
      Brush j (C* |q|) 1 (fun x=>∑ i∈O,A x i) y := by
    apply (Brush.spree O _ _ zero_le_one he).climb _ le_rfl
    rw [sum_const,nsmul_eq_mul]; gcongr
  let b i := -R.beta*(chalky (x i) (u i) V' Z + crispy (x i) Z)+e i + a i
  have hA' : Brush j ((Z.shares:ℝ)* S s) 1 b y := by
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
    have h := centralSum X' Z U u g V' hr (fun _=> rfl) (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
    have hv : Brush j ((Z.shares:ℝ)* D' s) 1 (fun i=> -R.beta*(chalky (x i) (u i) V' Z+crispy (x i) Z)) y := by
      apply (h.smul (-R.beta)).climb _ le_rfl
      rw [norm_neg,Real.norm_of_nonneg hr'.positive.le,hp.length_eq,hB']; unfold D'
      refine (mul_le_mul_of_nonneg_right (show R.beta ≤ 2*betaF G s L from hp.length_eq ▸ hr'.window.2) (by positivity)).trans_eq (by ring)
    refine ((hv.gathering (hh _ _ hI _ _ hC)).gathering (hh _ _ hj _ _ hg)).climb ?_ le_rfl
    unfold S; push_cast; unfold D'; apply le_of_eq; ring
  apply ((hA'.separating ((Brush.certified zero_le_one _).climb hA'.bound le_rfl)).climb _ le_rfl).shimmy (Eventually.of_forall fun i=>?_)
  · exact (le_of_eq (by ring : (Z.shares:ℝ)* S s+Z.shares*S s=(S s+ S s)*Z.shares)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _))
  let w := (X'.pens Z).card*Real.log (measure_g Ñ R.beta)
  have h y : f' y=b y-w := by unfold f' b plumeLog w e a; rw [hx']; rfl
  change f' i-f' y=b i-b y; rw [h,h]; abel
end YM.ConnectedActivityE6.Blaze.Silica.Clutch
