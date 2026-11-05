import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Stained
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Symplex

/-!
# Unmasked script rotor. Includes physical Ωℂ and all stock scores.

Gauge comparisons on off-threshold SAME masks, on anti-crystals only.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Stained
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond  Eider  Hues Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d : ℝ} {Ñ : ChartRatio G}
variable (X : Coat T F) (z : Site c→ G.El) (p : P.Funds S T) (h : ShellAccess S G X.x W X.width d)

lemma patchwork (u : Directions G f) (a : ℝ) (i : Bond f) : Polar.patch (sluice X z) a (spinRow S z u) i=Polar.patch X a u i := by unfold Polar.patch; rw [binding]; rfl
lemma priceHalo (hÑ : LocalRatio Ñ) (hp : 0 < a*X.t) (hx : 4*a*X.t < Ñ.radius)
    (i : Bond f) (u : Directions G f) :
    (sluice X z).gentry Ñ a (spinRow S z u) i=X.gentry Ñ a u i := by
  unfold gentry; rw [binding]
  by_cases he : X.cone (2*a) u i=0
  · rw [he,zero_mul,zero_mul]
  have hf : u i∈Metric.ball (0:G.Color) Ñ.radius := by
    have he := X.amount (show 0 < 2*a*X.t by rw [mul_assoc]; positivity) _ _ he
    apply Metric.mem_ball.mpr; rw [dist_zero_right]; nlinarith only [hx,he]
  change _ * Real.log (Ñ.J (skew (z _) (u i)))= _
  rw [keyship hÑ _ _ hf]
private lemma restrictW (j : Bond f) (u) : (fun i : G.ColorIndex=> (Hues.sheen X z*ᵥ u) (j,i))= Itinerary.restrict (Hues.sheen X z) j j *ᵥ fun i=> u (j,i) := by
  funext i; simp only [Matrix.mulVec, dotProduct]; rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rfl
  · intro b _ h; apply sum_eq_zero; intro l _; simp only [Hues.sheen, Rotation.off (z ∘ atEdge S) (j,i) (b,l) (show j≠b from Ne.symm h),zero_mul]
  simp
lemma respects {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℝ) (he : Hᵀ*H=1) (u v : ι→ℝ) :
    dotProduct (H *ᵥ u) (H *ᵥ v)=dotProduct u v := by
  have ht : Hᵀ *ᵥ (H *ᵥ v)=v := by rw [Matrix.mulVec_mulVec,he,Matrix.one_mulVec]
  conv_rhs => rw [← ht, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
include p h
lemma spinsHue (v : Hue X) (u : Directions G f) (b : Air f G) (a : ℝ) (i : ChainIndex f) (R : Rep G f) :
    Polar.spins (sluice X z) a R (spinRow S z u) (weep X z b) i=Polar.spins X a R u b i := by
  obtain ⟨h₁,h₂,h₃⟩:= royals X z p v; let Y:= sluice X z; let E := Hues.sheen X z; let J:= weep X z b
  let v:=spinRow S z u
  have hQ i : (Itinerary.restrict E i i)ᵀ*Itinerary.restrict E i i=1:= Hues.pools i (Rotation.off (z ∘ atEdge S)) (inverse_up _)
  rcases i with i|i|i|i|i
  · exact congr_arg (fun x=> -x/2) (h₁ i)
  · exact congr_arg (fun A=> ArmA X.shutter A i/2) (neutral Y X rfl)
  · exact congr_arg (fun x=> x/2) (h₂ i)
  · obtain ⟨hk,hx,-⟩:= fastens X p h z
    have hf : shimmer Y R.beta=E*ᵥ shimmer X R.beta := by
      unfold shimmer; rw [Matrix.mulVec_smul,hx,hk,Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        show Y.plate*E=E*X.plate from plate_con X z p]
    change Polar.patch Y a v i*dotProduct (fun j:G.ColorIndex=> J (i,j)) (fun j=>shimmer Y R.beta (i,j))=Polar.patch X a u i * dotProduct (fun j:G.ColorIndex=> b (i,j)) (fun j=>shimmer X R.beta (i,j))
    rw [patchwork X z u,hf,show (fun j:G.ColorIndex=> J (i,j))=_ from restrictW X z i (WithLp.ofLp b),restrictW X]
    rw [respects _ (hQ i)]
  change entangled Y a v J i=entangled X a u b i; unfold entangled; rw [patchwork X z u,patchwork X z u]
  apply congr_arg; unfold qunique circle; apply congr_arg; let q:= i.2.1; let l:= i.2.2; let j:= arrive q l
  let K:= combo q l (X.finale i.1); let L:= combo q l (Y.finale i.1); let B:= Itinerary.restrict E q q; let C:= Itinerary.restrict E j j
  have he : L*C=B*K := by
    refine combo_respects q l (Rotation.off (z ∘ atEdge S)) _ _ ?_; intro t _; unfold finale; split
    next hr => rw [neg_mul,mul_neg, show Y.shreds*Hues.sheen X z = Hues.sheen X z * X.shreds from shredsG X z p]
    next => exact plate_con X z p
  let w (j : Bond f) (k:G.ColorIndex) := b (j,k)
  have hh : (fun k:G.ColorIndex=> J (j,k))= C *ᵥ w j := restrictW X z j _
  have hx : (fun k:G.ColorIndex=> J (q,k))= B *ᵥ w q := restrictW X z q _
  change dotProduct (fun k:G.ColorIndex=> J (q,k)) (L *ᵥ fun k:G.ColorIndex=> J (j,k))=dotProduct (w q) (K *ᵥ w j)
  rw [hx,hh,Matrix.mulVec_mulVec,he, ← Matrix.mulVec_mulVec]; exact respects _ (hQ q) _ _

lemma upwind (u : Directions G f) (s : Signed) (i : Spot c f) (e : Bool) :
    let Y:= sluice X z; let v:=spinRow S z u
    rootface Y v (Y.input v) e s i=rootface X u (X.input u) e s i ∧ Vine.costs Y v s i=Vine.costs X u s i := by
  intro Y v
  have he : Vine.costs Y v s i=Vine.costs X u s i := by unfold Vine.costs; refine sum_congr rfl fun j _=> ?_; unfold pot; rw [reroot X p h z u,G.norm_adjoint]; rfl
  let t : Site c→G.El := z ∘ Lattice.affine s 0
  have hF : pull s 0 (Y.input v)=gauge (constantGauge t S.ratio) (pull s 0 (X.input u)) := by
    rw [banks X z u,Work.F05.pull_gauge_zero]; have hk : (fun x:Site f=>constantGauge z S.ratio (Lattice.affine s 0 x))=constantGauge t S.ratio := by
      funext j; simp only [constantGauge,t,affine0,Function.comp_apply]; rw [S.ratio.parent_signed S.patch.odd_side]
    rw [hk]
  unfold rootface; rw [he,hF, show pull s 0 Y.V=gauge t (pull s 0 X.V) from Work.F05.pull_gauge_zero .., winds t _ (pull s 0 X.V) p]; exact ⟨rfl,rfl⟩
lemma flight (β : ℝ) (w : Air f G) : worldZ (sluice X z) β (weep X z w)=spinRow S z (worldZ X β w) := by
  unfold worldZ; rw [(fastens X p h z).2.2, show (sluice X z).atmos (weep X z w)=_ from (atmospheric X z w)]
  funext; simp only [spinRow,Pi.add_apply,Pi.smul_apply,map_add,map_smul]
omit p h
lemma perF (e : Intake P T X.x R) (a : ℝ) (u : Directions G f) (i : LogLetter c f) :
    let Y:= sluice X z; let v:=spinRow S z u
    Polar.frost Y a R v (Y.input v) i=Polar.frost X a R u (X.input u) i := by
  intro Y v
  have hh := inhalesG X z u e a i
  rcases i with i|i|i|i|i|i <;> try exact hh
  unfold Polar.frost; rw [Hues.mandate X z (2*a) u]; unfold nest; dsimp only [Sum.elim]
  unfold icicle Polar.twin; simp only [show Y.V=gauge z X.V from rfl, Work.F05.pull_gauge_zero,PathData.ellTerms,Work.F05.slot_gauge, ← map_smul,Hues.duet]; rfl
variable (e : Intake P T X.x R) (l : ℕ) (s : Finset ℕ)
include h e
lemma fights (hÑ : LocalRatio Ñ) (ha : 0 < a*X.t) (hx : 4*a*X.t < Ñ.radius) (hp : Hue X) (u : Directions G f) (w : Air f G) (i : Head S) :
    let Y:= sluice X z; let v:=spinRow S z u
    ember Y a R W Ñ v (Y.input v) (weep X z w) s l i=ember X a R W Ñ u (X.input u) w s l i := by
  intro Y v
  have hF := e.ready
  have hS p : Y.gentry Ñ a v p=X.gentry Ñ a u p := priceHalo X z hÑ ha hx p u
  have hP p : Y.condensation p=X.condensation p := (royals X z e.ready hp).2.2 p
  have he y i : Vine.costs Y (voltage Y) y i= Vine.costs X (voltage X) y i := by rw [(fastens X hF h z).2.2]; exact (upwind X z hF h _ _ _ false).2
  rcases i with i|i|i|i
  · change (if Packets.connected S l X.B i then _ else _)=(if Packets.connected S l X.B i then _ else _); split
    next ht=> unfold Polar.stock; rw [show Y.seeds=X.seeds from rfl]; split
              next hf => dsimp only; let p:=300*X.B; let Q:= X.plaza (i.dome (304*X.B))
                         have hQ : plumeLog Y a R Ñ v (Y.input v) i= plumeLog X a R Ñ u (X.input u) i := by
                           unfold plumeLog chalky crispy; have hU s j : rootface Y v (Y.input v) false s j=rootface X u (X.input u) false s j := (upwind X z hF h u s j false).1; simp only [show Y.B=X.B from rfl,hU,he,hP,hS]; rfl
                         rw [hQ,Hues.mandate X z a u]; apply congr_arg₂ (·*·) _ rfl
                         have hz p : Y.rawStorm v W i R s p=X.rawStorm u W i R s p:= storm_g X z u (funds_branch e.ready) ..
                         have hv : Contract.order R s (vias S i p) (Y.input v)*tickets i p (Y.input v) X.k*profiles i X.χ p X.x W (Y.input v) X.k (gauge z X.V) =
                             Contract.order R s (vias S i p) (X.input u)*tickets i p (X.input u) X.k*profiles i X.χ p X.x W (X.input u) X.k X.V := by
                           have hj:= Y.forceds i R s W v; dsimp only at hj; simp_rw [hz] at hj; exact hj.symm.trans (X.forceds ..)
                         simp only [mul_assoc] at hv
                         simp_rw [mul_assoc]; exact congr_arg (fun x:ℝ=> Real.exp (plumeLog X a R Ñ u (X.input u) i) * x) hv
              rfl
    next => rfl
  · have ht : R.activities.K i (Y.input v)=R.activities.K i (X.input u) := by rw [banks X z u]; exact e.cap.labels.forced.sym ..
    exact congr_arg₂ (·*·) ht (Hues.mandate X z _ u (Y.plaza (forcedFoot S.ratio 0 Y.B R i)))
  · refine congr_arg (fun x:ℝ=>Real.exp x-1) (show logMoment Y a R Ñ v (Y.input v) (weep X z w) i = _ from ?_)
    rcases i with i|i|i
    · exact perF X z e a u i
    · rcases i with i|i|i
      · change hover Y a R v (Y.input v) i=hover X a R u (X.input u) i
        unfold Polar.hover; dsimp only; rw [Hues.mandate X z (2*a) u, (upwind X z hF h u _ _ true).1, he]; rfl
      · change (if voyage X.seeds (200*X.B) i then 0 else Y.condensation i)=X.undercurrent i; unfold undercurrent; rw [hP]
      change (if i∉_ ∧ X.Hot i then Y.gentry Ñ a v i else 0)= X.solo u Ñ a i; unfold solo; rw [hS]; rfl
    exact spinsHue X z hF h hp u _ _ _ R
  have hi X (p : WarningAt c f) (u:Directions G f) : sprinkle X a R W u (X.input u) s p=Coat.detect (F:=F) (T:=T) X u W a R s p := by
    cases p
    · rfl
    rfl
  change sprinkle Y a R W v (Y.input v) s i =sprinkle X a R W u (X.input u) s i; rw [hi,hi, flags_g X z u (funds_branch e.ready)]
end YM.ConnectedActivityE6.Blaze.Stained
