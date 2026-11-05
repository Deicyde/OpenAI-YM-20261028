import YM.UVExtension.Wick.Prize

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}

section toll
variable {k:Mixed.Costs} (hp:k.Buy S.patch.L Q.halo (radiusB x))
-- absorb at the union-level exponent (not support-confused). 
lemma sale_coast {p:Molecule S→ℝ} (l : ℝ) {v:ℝ} (h : Ac.Hit H.unionP (radiusB x) p u v) : Ac.Hit H.unionP (radiusB x) (fun i=> Real.exp (l*coverNumber (radiusB x) (H.unionP i))*p i) (u-l) v := by
  intro x; convert h x using 1; ext i; split <;> try rfl
  dsimp only; rw [mul_comm (Real.exp (l*_)),mul_assoc, ← Real.exp_add]; ring_nf
-- hit-to-single needs nonempty! total nonzero at unused empty support not implied.
lemma own_price {p:Molecule S→ℝ} {v:ℝ} (h : Ac.Hit H.unionP (radiusB x) p u v) (hu:0≤u) (i:Molecule S) (he:(H.unionP i).Nonempty) :p i ≤ v:=by
  obtain ⟨j,hj⟩:=he; have ht:=budget_single (h j) i; simp only [hj,↓reduceIte] at ht; by_cases hh:0≤p i; swap; · exact (le_of_not_ge hh).trans (budget_nonneg (h j))
  exact (le_mul_of_one_le_right hh (Real.one_le_exp (by positivity))).trans ht
end toll

def cashBox (H:Cash W x μ L Q o a T R) (X:Coat T F) (V:ι→ Juice G f) (p:Molecule S) (t:Vines ι) :=
    ∫ i,subtend X R W o.a Q.table Q.halo (H.unionP p) V p t i ∂((F.order G).prod volume)

def bubble (H:Cash W x μ L Q o a T R) (V:ι→ Juice G f) (X:Coat T F) (p:Molecule S) (t : Vines ι):ℂ:=
    if Matter.standsIn X R Q.halo p then ((Fintype.card S.Choices:ℂ))⁻¹* ∑ i,cashBox H ((planted X p).taggedL i) V p t else 0

namespace Festa
variable {X} (K : Festa Q L H V b B) (hx : X.x=x) (hX:X.width=o.K) (hm:X.manifest) (p:Molecule S)
local notation "Σ" => parade (ι:=ι) (betaF G x L) B
local notation "φ" => gush X R W o.a Q.table Q.halo V p
local notation "Kp" => podium S G (H.unionP p) X.B
local notation "plane" => grounds (ι:=ι) (betaF G x L) b
local notation "Λ" => grown (ι:=ι) (betaF G x L) b
set_option quotPrecheck false
local notation "Γ" => (F.order G).prod X.dice
local notation "Δ" => (F.order G).prod (volume : Measure (Body (↥Kp)))
local notation "A" => subtend X R W o.a Q.table Q.halo (H.unionP p) V p
variable {t : Vines ι} {H': Cash W x μ L Q o a T (flight R (t none).re)}
include K hx hX hm
lemma gearV (X': Drums ι) (he: Λ X') : cashBox H X V p (hoist X')= X.attains (chunk R (blend V (X'∘some)) (X' none)) Q.table W o.a (Matter.own p) Q.halo p:= by
  let z:= hoist X'; let u:= X' none
  have hp := (H.laws.data.localP _ X hx hX hm).sails.fullC
  let R':= chunk R (blend V (X'∘some)) u
  let I:= Kp; let c':= Pond.circuit I X.relating
  let H':= (K.mixture X' he).some
  have hd:c'.PosDef:= hp.submatrix Subtype.val_injective
  have hu:0<u := breath (altitude (H:=H)) (show ((u:ℂ))∈ aisle _ from he none)
  let f i:= X.body R' Q.table W o.a (Matter.own p) Q.halo p i; let g (i:F.Slice G × Body (↥I)):ℝ := f (i.1,Pond.spill I i.2)
  have hf:Measurable f:= X.body_b Q.table_exists (hx.symm ▸ H'.laws.intake) (by rw [hx,hX]; exact H.laws.data.access) _ _ _ _
  have hg: Measurable g:= hf.comp (measurable_fst.prodMk ((spill_m I).comp measurable_snd))
  unfold cashBox attains
  have hh (i:F.Slice G× Body (↥I)) : A z i= (↑(tether c' u g i:ℝ):ℂ):= by
    unfold subtend; rw [real_val (H:=H) X p X' he]; rw [show z none = (u:ℂ) from rfl,voiced _ _ hu]
    rw [tether]; unfold g; dsimp only; rw [Festa.spilling,smul_eq_mul]; push_cast; rfl
  change (∫ i,A z i ∂Δ)= Complex.ofReal (∫ i,f i ∂Γ)
  simp_rw [hh]; rw [integral_complex_ofReal,← axle _ c' hd hu]; apply congr_arg Complex.ofReal
  let μ:=(F.order G).prod (arch I X.relating); let p:= sweeping X I hp
  change (∫ i,g i ∂μ)=_; rw [show μ=Measure.map _ Γ from p.map_eq.symm, integral_map p.measurable.aemeasurable hg.aestronglyMeasurable]; apply integral_congr_ae; filter_upwards with v
  exact H'.concord _ (X.wrapY v.1) (X.wrapY v.1) (show Borough _ _ (H.unionP _) (Pond.spill I (Pond.swim I v.2)) v.2 _ _ _ from ⟨Village.refl ..,(observe I).1 (Pond.settled ..),fun _ _=>Iff.rfl⟩) hx (Finset.Subset.refl _)
omit hm in
lemma real_money (X': Drums ι) (he:Λ X') : bubble H V X p (hoist X')=Matter.proceedsA (chunk R (blend V (X'∘some)) (X' none)) X W o.a Q.halo Q.table p := by
  unfold Matter.proceedsA bubble
  have hv : Matter.standsIn X R Q.halo p ↔ Matter.standsIn X (chunk R (blend V (X'∘some)) (X' none)) Q.halo p:= Iff.rfl
  rw [hv]; split; swap; · rw [Complex.ofReal_zero]
  have hf i : cashBox H ((planted X p).taggedL i) V p (hoist X')=_:= K.gearV (X:=((planted X p).taggedL i)) hx hX (planted_valid ..) p X' he
  simp_rw [hf]; unfold amountP levelMean likely; push_cast; rfl

variable {q : Q.rate≤γ} {hh' : γ<0}
local notation "χ" => stalk Q q hh'
variable {v'} (N : Copal H' ((stalk Q q hh').costs L μ (t none).re x v') V B (t none))
variable (l:ℝ)
-- prices without union pay, after spare support.
def fawn (j:ℕ) (p : Molecule S):= Real.exp (l*coverNumber (radiusB x) (H'.unionP p))*Mixed.selected S Q.halo (radiusB x) ((stalk Q q hh').costs L μ (t none).re x v') H'.birth N.fee (lengths T R) (steamP S ((stalk Q q hh').costs L μ (t none).re x v')) 0 0 j 0 p
omit K hm hx hX in
lemma fawn_nn (j:ℕ) (p : Molecule S) : 0 ≤ fawn N l j p:= by
  unfold fawn Mixed.selected; apply mul_nonneg (Real.exp_pos _).le; split
  next h => refine Mixed.zero_le_price S Q.halo (radiusB x) _ _ _ (lengths T R) _ ?_ N.added 0 p; rw [H'.laws.data.funds.length_eq]; exact N.paper
  exact le_rfl
variable (hQ : ∀ (i:Molecule S), permag (t none) (podium S G (H.unionP i) (radiusB x)).card ≤ Real.exp (l*coverNumber (radiusB x) (H.unionP i)))
omit K hx hX hm in
lemma profit (j:ℕ) : Ac.Hit H.unionP (radiusB x) (fawn N l j) (Q.exp-l) ((stalk Q q hh').quantum L μ x 0 0 j 0) := by
  have ht:=H.laws.data.funds.length_eq
  apply sale_coast (p:=fun p=> Mixed.selected S Q.halo (radiusB x) ((stalk Q q hh').costs L μ (t none).re x v') H.birth N.fee (lengths T R) (steamP S ((stalk Q q hh').costs L μ (t none).re x v')) 0 0 j 0 p) l
  refine Mixed.mixed_hit S Q.halo (radiusB x) ((stalk Q q hh').costs L μ (t none).re x v') _ _ (lengths T R) _ ?_ N.added 0 0 j 0
  rw [ht]; exact N.paper

include hQ
lemma reward (ht:t∈Σ) (hp : Ac.Spark H.supportP p) (j:ℕ) (h : j ≤ Cash.numP p) :
    Integrable (A t) Δ ∧ (∫ i, ‖A t i‖ ∂Δ)≤ fawn N l j p := by
  obtain ⟨hv,hy⟩:= K.value_toll X hx hX hm p N ht
  have hp : Mixed.Allowed S Q.halo (radiusB x) ((stalk Q q hh').costs L μ (t none).re x v') H'.birth (lengths T R) 0 j 0 p:= ⟨hp,Nat.zero_le _,h,H'.positive_volume _⟩
  unfold fawn Mixed.selected; rw [if_pos hp]; refine ⟨hv,hy.trans ?_⟩
  unfold Mixed.Price; rw [pow_zero,mul_one]
  have hh: X.B=radiusB x:= congr_arg _ hx; apply mul_le_mul_of_nonneg_right (show permag (t none) (Kp).card ≤ _ from (by rw [hh]; exact hQ p)) (prod_nonneg fun i hi=> ?_)
  rcases i with i|i
  · unfold tabs Mixed.costs; dsimp only [Sum.elim]; split; next hx=> exact mul_nonneg N.paper.capture (Real.exp_pos _).le
    next => exact le_rfl
  exact N.added.holds _
end Festa
end YM.UVExtension.Wick
