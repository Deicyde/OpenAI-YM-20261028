import YM.FullVolume.Sector.Count
/-! Stamped weights on a Tune.Coverage -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R} -- implicit v
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' f':ℝ} {K:ℕ} {χ:Chi}
-- All posts including the line; M∈path coupling. Keep same order, signs and all predicates.
structure Lyre (U:Tune H v δ) (j:ℕ) (u d r C':ℝ) (χ:Chi) (A b L':ℝ) (k:ℕ) where
  pole : Plot H j u d r C' χ A b L' k
  plot (t:ℝ) (h: |t|≤ 6*v) : Plot (U.beams t h) j u d r C' χ A b L' k
namespace Lyre
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
local notation "ψ" => U.pole
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "Λ" => U.pole
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)
-- Label explicitly types.
def vertex (_M:Lyre U j u d r A' χ A b L' K) (X:Coat T F) (V:E→ Config G c) (z:Air f G) (L:Finset ℕ) (i:Head S) (t:ℝ) (x:E):= Polar.ember (vary X (V x)) o.a (U.notes t) W Q.table (steer X A (worldZ X R.beta z) (V x)) (X.input (worldZ X R.beta z)) (U.pole.flow t • (course X A R.beta z (V x))) L Q.halo i
include M hx he hv hm hy hU
-- h posts
lemma emitted {i:ℝ}(hi:|i|≤6*v) (p:Head S) (f:Finset ℕ) (hp : Healthy (Pressure.temp X.x) (H.supportP p) X.V):
    Brush j ((M.plot i hi).stencil.tag p) (r * spanW T R w₀ Q.halo p) (fun x=> M.vertex X U₀ z f p i x) s:=by
  let h:= M.plot i hi; let P:= U.notes i; have ht:=U.seats i hi; let ζ:= Λ; let z':=ζ.flow i • z
  let V r := steer X A (worldZ X P.beta z') (U₀ r); let Z r:= course X A P.beta z' (U₀ r)
  have hZ : Clutch X z' o.a P.beta d s j U₀ V Z:= ((M.plot i hi).rays F X hx he hv hm E U₀ s hy hU).2 z'|>.1
  have hr:=h.stencil.stream E F X U₀ V Z s z' hx he hv hm hU hZ f p ((U.arena i hi) ▸ hp)
  rw [U.tune_span i hi]
  have hΔ:X.B=radiusB x₀:=congr_arg _ hx
  simp_rw [hΔ] at hr
  refine hr.shimmy (Eventually.of_forall fun y=>?_)
  have hh:worldZ X P.beta z'=worldZ X R.beta z:=by unfold z' ζ; rw [← U.pitch i hi]; exact moving ht ..
  have ht':Z y=ζ.flow i • course X A R.beta z (U₀ y):=by unfold Z z' ζ; rw [← U.pitch i hi]; exact coursing ht ..
  change vertex M X _ _ _ _ _ y= Polar.ember _ _ P _ _ (V y) _ (Z y) _ _ p
  unfold vertex V; rw [hh,ht']
-- Monomial stamp. Keep cost in shares even on undecided pen counts (aperture).
omit M hx he hv hm hy hU
lemma momentum {A' : ℝ} (i:ℝ) (h: |i|≤6*v):
    (Q.costs L μ β x₀ A').gain ≤ (Q.costs L μ (U.notes i).beta x₀ A').gain:=by
  have hp := (U.seats i h).pos
  have hu:= U.plot_rel i h
  have hv:= ((Λ).moves i h).1
  let a:=μ* Pressure.fiery G x₀ L^2; have ha:0≤ a:= mul_nonneg H.laws.data.μ_pos.le (sq_nonneg _)
  change β*a≤ _; apply mul_le_mul_of_nonneg_right _ ha
  rw [hu]; exact le_mul_of_one_le_right hp.le (one_le_pow₀ hv)
private lemma helenS {i:ℝ} (hp:|i|≤6*v) (p:Stores S) (f:Finset ℕ) : steamP S (Q.costs L μ (U.notes i).beta x₀ A') p ≤ steamP S (Q.costs L μ R.beta x₀ A') p:=by
  unfold steamP Packets.income; apply mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (sub_le_sub_left ?_ _) (Nat.cast_nonneg p.shares))) (show (0:ℝ)≤1 from zero_le_one); exact momentum (U:=U) i hp
include M hx he hv hm hy hU
lemma actors (f:Finset ℕ) (p:Stores S) (h: Packets.connected S Q.halo w₀ p) (hp: Healthy (Pressure.temp X.x) (H.supportP (Sum.inl p)) X.V) :
    Weigh j s v (FullVolume.Ray.Fold.charge j * (1+δ)^(Tune.count X p)*steamP S (Q.costs L μ R.beta x₀ A') p) r (fun t x=> vertex M X U₀ z f (Sum.inl p) t x) := by
  let fz:= f₀; let y:= I₀; let P i := Polar.stock (vary X (U₀ i)) o.a R W Q.table (fz i) y f p
  let Q' i:= β * (Polar.chalky (vary X (U₀ i)) (fz i) y p+Polar.crispy (vary X (U₀ i)) p); let F:= FullVolume.Ray.Fold.jet (Λ) P Q' (Tune.count X p)
  have hΞ:= h; rw [← (show X.B=w₀ from congr_arg _ hx)] at hΞ
  have hZ t (ht : |t|≤6*v) : vertex M X U₀ z f (Sum.inl p) t= F t:= by
    funext i; unfold vertex F; change (if Packets.connected S Q.halo X.B p then _ else 0)=_
    rw [if_pos hΞ]; exact U.lit _ _ ht ..
  let t:= M.pole; let q:= Q.costs L μ R.beta x₀ A'; have hP:X.B=w₀:=congr_arg _ hx
  let V i:= X.enforce o.a (fz i) (X.plaza (p.dome (304*X.B)))
  have hf : 0≤ steamP S q p:= by
    change 0≤ 1 * Real.exp _; positivity
  have ha := M.pole.stencil.active
  by_cases hg: V=ᶠ[𝓝 s] fun _=>0
  · have hh: P=ᶠ[𝓝 s] fun _=>0:=by
      filter_upwards [hg] with i hi; unfold P Polar.stock; split
      · change _ * V i=0; rw [show V i=0 from hi,mul_zero]
      rfl
    refine (FullVolume.Ray.Weigh.loses (FullVolume.Ray.Weigh.zero (U.normed) (b:=r) (zero_le_one.trans ha)) ?_ le_rfl).cong ?_
    · apply mul_nonneg _ hf; have hy := (Λ).full.2.2
      exact mul_nonneg ((FullVolume.Ray.ink.pay_pos _).trans (le_max_left ..)) (by positivity)
    intro i hi; rw [hZ i (U.lay hi)]; filter_upwards [hh] with x hx; change P x * _ * _=_; rw [show P x=0 from hx,zero_mul,zero_mul]
  refine FullVolume.Ray.Weigh.cong (g:=fun i t=> F i t) (FullVolume.Ray.Fold.scores ?_ ?_ hf (zero_le_one.trans ha) ?_) (fun i hi=> EventuallyEq.of_eq (hZ i (U.lay hi)))
  · let Z:= z₀; have he':= M.pole.stencil.stream E _ X U₀ fz Z s z hx he hv hm hU ((M.pole.rays _ X hx he hv hm E U₀ s hy hU).2 z|>.1) f (Sum.inl p) hp
    apply he'.smooth.congr_of_eventuallyEq; exact Eventually.of_forall fun i=> (if_pos hΞ).symm
  · exact contDiffAt_const.mul ((M.pole.pays E _ X z R.beta U₀ fz _ s p y hx he hm hv hU ((M.pole.rays _ X hx he hv hm E U₀ s hy hU).2 z|>.1) hg).smooth)
  intro i; let a := v*(Λ).seat (Q' s) i; have h' : |a|≤6*v:= U.away ..
  change Brush _ _ _ (F a) _
  rw [← hZ _ h']
  let x':= (M.plot a h').stencil; have hc:= emitted M X hx he hv hm hy hU z h' (.inl p) f hp
  have hC: (x'.tag (.inl p))= steamP S (Q.costs L μ (U.notes a).beta x₀ A') p:= if_pos h
  change Brush _ (x'.tag _) (r*1) _ s at hc
  rw [hC,mul_one] at hc; exact hc.climb (by apply helenS h' p f) le_rfl
end Lyre
end YM.ConnectedActivityE6.Empire
