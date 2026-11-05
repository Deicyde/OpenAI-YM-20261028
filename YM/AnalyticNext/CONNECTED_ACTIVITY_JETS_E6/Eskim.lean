import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Armor
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pommel

/-!
# Shift for all data, held-U motion. Also on auxiliary extended moments

 PSA arbitrary Motion on finite directions investigated with true phases;
 Jacob factor purchased later. Can step on all bonds even if not needed
 on lumbar. `Drive` moving from ORIGINAL V pack, use uniform neighborhood
 over Y,k before all masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Silica
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Raw Matter Scroll Vine Polar Frond Eider Brush
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : E→Config G c} {x : E}
variable {a α β γ d η σ : ℝ} {j : ℕ} {A : ℝ}

def action (X : Coat T F) (V : Config G c) (i : Bond f) := replica S.ratio X.V i*(replica S.ratio V i)⁻¹
def steer (X : Coat T F) (d : ℝ) (u : Directions G f) (V : Config G c) : Directions G f := fun i=>
    fleece G X.χ d (G.mat (action X V i)) (u i)
def steerJ (X : Coat T F) (d : ℝ) (u : Directions G f) (V : Config G c) (i : Bond f) :=
    palm G X.χ d (G.mat (action X V i)) (u i)
def course (X : Coat T F) (d β : ℝ) (z : Air f G) (V : Config G c) : Air f G :=
    WithLp.toLp 2 <| stand <| (gStep β)⁻¹ • (steer X d (worldZ X β z) V - voltage (vary X V))

variable (X : Coat T F) (p : Canary G d A)

lemma proceeds (d : ℝ) (he : 0<β) (z : Air f G) (V : Config G c) :
    worldZ (vary X V) β (course X d β z V)=steer X d (worldZ X β z) V := by
  rw [worldZ]
  rw [show (vary X V).atmos _=(gStep β)⁻¹ • (steer X d (worldZ X β z) V - voltage (vary X V)) from (rfl : (vary X V).atmos (course X d β z V)=(gStep β)⁻¹ • (steer X d (worldZ X β z) V-voltage (vary X V))),
    smul_inv_smul₀ (show gStep β≠0 from (inv_pos.mpr (Real.sqrt_pos.mpr he)).ne')]; abel
include p in lemma home (z : Air f G) (h : 0 < β) : course X d β z X.V=z := by
  let g:= gStep β; have he:g≠0 := (inv_pos.mpr (Real.sqrt_pos.mpr h)).ne'
  let u:= worldZ X β z
  have hf : steer X d u X.V=u := by funext i; simp [steer,action,nothing_f p]
  unfold course; rw [hf]; change WithLp.toLp 2 (stand (g⁻¹ • (u-voltage X)))=z; unfold u worldZ
  rw [add_sub_cancel_left, inv_smul_smul₀ he]; rfl

structure Drivable (X : Coat T F) (d A : ℝ) (V : Config G c) : Prop where
  good (i : Bond f) :
    let M := G.mat (action X V i)
    ‖M-1‖ < A ∧ Bijective (fleece G X.χ d M) ∧ ∀ x:G.Color, ‖plume G X.χ d M x‖< d/2 ∧ 0 < palm G X.χ d M x

lemma chargeMode (χ : ℝ) (h : Mode V x j χ) (i) : Brush j (royalty G) χ (fun y=>G.mat (action X (V y) i)) x := by
  simpa only [mul_one] using! offsetB (Blaze.reverse (f:=fun y=>replica S.ratio (V y) i) (recopy S h.atLink i)) (replica S.ratio X.V i) 1
include p
lemma nearby (hv : V x=X.V) (h : Mode V x j σ) : ∀ᶠ y in 𝓝 x, Drivable X d A (V y) := by
  apply (Filter.eventually_all.mpr (?_ : ∀ i:Bond f,∀ᶠ y in 𝓝 x, let M:=G.mat (action X (V y) i); ‖M-1‖<A ∧
    Bijective (fleece G X.χ d M) ∧ ∀ x, ‖plume G X.χ d M x‖<d/2 ∧ 0<palm G X.χ d M x)).mono (fun y hy=> ⟨hy⟩)
  intro i
  have he := vies p X.χ
  have hM : Tendsto (fun y=> G.mat (action X (V y) i)) (𝓝 x) (𝓝 1) := by
    rw [← show G.mat (action X (V x) i) = 1 by rw [hv,action,mul_inv_cancel,G.mat_one]]
    exact (chargeMode X σ h i).smooth.continuousAt
  exact hM.eventually he

-- At every position (including unobserved). Works at truncated u as well.
lemma conquered (V : Config G c) (u : Directions G f) (h : Drivable X d A V) (hp : 0<a*X.t) (he : 8*a*X.t ≤ d/2) :
    Armor (vary X V) (2*a) (steer X d u V) ((vary X V).input (steer X d u V)) (X.input u) := by
  refine ⟨fun i hh=>?_,(by change 0<2*a*X.t; rw [mul_assoc]; positivity)⟩
  by_cases hg : X.Hot i
  swap; · exact ((vary X V).dormant _ _ hg).trans (X.dormant _ _ hg).symm
  let v:= steer X d u V; let W:=vary X V
  obtain ⟨hr,hH,hY⟩:= h.good i
  let M:=action X V i; let z:=plume G X.χ d (G.mat M) (u i)
  have ht : ‖v i‖ ≤ d/2 := (hh.resolve_left (not_not.mpr hg)).trans (by change 4*(2*a)*X.t≤_; nlinarith only [he])
  have hU : ‖u i‖ ≤ d := by
    have hp' : u i=v i-z := (by unfold v steer fleece z; rw [add_sub_cancel_right])
    rw [hp']; have hx : ‖z‖ < d/2 := (hY (u i)).1
    exact (norm_sub_le ..).trans (by linarith)
  have hv : G.lieExp (v i)=G.lieExp (u i)*M := sustaining p X.χ hU M hr.le
  change W.input v i=_; rw [W.viewing v i hg,X.viewing u i hg]; unfold increment; rw [hv]; unfold M W action; change _ * replica S.ratio V i=_; group

omit X p in lemma plastic {X : Coat T F} {U V : Config G f} {u : Directions G f} (p : Armor X (2*a) u U V) (h : 0<a*X.t) : Armor X a u U V := by
  have hp:4*a*X.t≤4*(2*a)*X.t := by nlinarith
  exact ⟨fun i hi=> p.same i (hi.imp_right fun hx=> hx.trans hp),h⟩

-- Dynamical point variation in the product. Freezing compulsory decisions.
structure Clutch (X : Coat T F) (z : Air f G) (a β s : ℝ) (x : E) (k : ℕ) (U : E→ Config G c)
    (u : E→ Directions G f) (w : E→ Air f G) : Prop where
  atV : U x=X.V
  beta : 0<β
  birth : w x=z
  pulse : 0<a*X.t
  moving : ∀ y,worldZ (vary X (U y)) β (w y)=u y
  price : 0≤s
  bud (i : Bond f) : Brush k s 1 (fun y=> u y i-worldZ X β z i) x
  patch : ∀ᶠ y in 𝓝 x, Armor (vary X (U y)) (2*a) (u y) ((vary X (U y)).input (u y)) (X.input (worldZ X β z))

omit X in
lemma clips (P : Teller G) (L : Side) (j : ℕ) (χ : Chi) {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) :
    ∃ B D, Rate G L (-(1/2)) B ∧ Rate G L 0 D ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F), X.x=x → Works P L x S T → X.χ=χ → ∀ β>0,
      ∀ z : Air f G, ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c) (y:E), U y=X.V → Mode U y j (V x) →
        let u:=worldZ X β z
        (∀ i,Brush j 1 (D x) (fun v=>steerJ X d u (U v) i) y) ∧ (∀ a : ℝ, 0<a*X.t → 8*a*X.t ≤ d/2 →
          Clutch X z a β (|B x|) y j U (fun v=> steer X d u (U v)) (fun v=>course X d β z (U v))) := by
  obtain ⟨A,b,H,hb,hX⟩:= cozies p χ j L h
  refine ⟨A,b,H,hb,hX.mono ?_⟩
  intro x h c f S T F X hk hr hχ β hβ z E _ _ U y ht hv u
  subst χ
  have hp (i:Bond f) := h E (fun v=>G.mat (action X (U v) i)) y (by rw [ht]; simp [action]) (chargeMode X (V x) hv i) (u i)
  refine ⟨fun i=> (hp i).2,fun a ha hF=> ⟨ht,hβ,?_,ha,fun v=> proceeds _ _ hβ _ _,abs_nonneg _,?_,?_⟩⟩
  · rw [ht,home X p z hβ]
  · intro i; unfold steer fleece; change Brush _ _ _ (fun v=> u i+_ -u i) _; simp_rw [add_sub_cancel_left]; exact
      (hp i).1.climb (le_abs_self _) le_rfl
  filter_upwards [nearby X p ht hv] with y hh; exact conquered X p (U y) u hh ha hF

end YM.ConnectedActivityE6.Blaze.Silica
