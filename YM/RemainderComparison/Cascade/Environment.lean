import YM.RemainderComparison.Cascade.Swell

/-!
# Substrate of the two budget books

One common apparatus for high and precision-tail epochs. Same measures even
on collars and singular flags. Surface demands only are different; prices
from `Utopia` *at that epoch*. This file is post-Cash; no assumption on Cash
from another uv example.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cascade
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {V:E→Config G c} {y:E} {f':E→Directions G f}{z':Air f G}{g:E→Air f G}
def Prints (H:Cash W x μ L Q o C T R) (k i:ℕ) (A:ℝ):Prop:= let _:=H; ∀ (ι κ e:ℝ),
    1≤e → 0≤ι → ι≤e*ballCost (radiusB x)*(Itinerary.density L:ℝ) → κ=ι*Fintype.card G.ColorIndex →
    (1+ι+κ+κ)^k*(1+κ*(2*Real.exp ((payE o.eta o.gap o.ample (tubularPrice G L))*(k:ℝ)^2/2))) ≤ A*e^i

/-- Ink test even if no mark is present. Active alarm buys all exact seeds. -/
lemma dries (ht:X.x=x)(hf:X.χ=χ)(hw:X.width=o.K)(he:X.manifest) (p:Molecule S)
    (j' l:ℕ) (F':ℝ) (hF:0 ≤ F') (hp:Prints H (j'*2) l F') :
    let I:= edgesM S (H.unionP p) (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p)
    let f (z:Air f G):= facescale I z^j'; let Q:= J.indicator f; let S':=1+H.shapeW p
    Integrable Q X.dice ∧ (∫ z,Q z ∂X.dice) ≤ ((1+F')*S'^l)*Ξ.rad^(blaze p).card := by
  intro I J f' Q' S'
  let h:= H.laws.data; have hh:= h.funds
  have hR:= h.localP F X ht hw he
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p)
  have hQ:MeasurableSet J := Poll.sounded ..
  have hm:=globes I hR.sails (j'*2)
  have hV := (globes I hR.sails j').1
  refine ⟨hV.indicator hQ,?_⟩
  let i':ℝ:= I.card; let V:ℝ:= (lensS I G).card
  have hI: i'≤ S'*ballCost (radiusB x)* (Itinerary.density L:ℝ) := by
    have h:= crewsC H p; rw [hh.length_eq] at h; apply h.trans; unfold S'; gcongr; linarith
  have ha: 1≤1+F':= le_add_of_nonneg_right hF
  have hV' : V=i'*Fintype.card G.ColorIndex := by simp [V,i',lensS]
  have hp := hm.2.trans (hp i' V S' hx' (Nat.cast_nonneg _) hI hV')
  have hc : ∫ x,f' x^2 ∂X.dice ≤ ((1+F')*S'^l)^2 := by
    unfold f'; simp_rw [← pow_mul]; apply hp.trans
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans hx') _)).trans
      (le_self_pow₀ (one_le_mul_of_one_le_of_one_le ha (one_le_pow₀ hx')) (by omega))
  refine divideC _ f' hV _ (by positivity) _ hQ (by rw [← pow_mul, Nat.mul_comm]; rw [pow_mul]; exact Ξ.ship _ X ht hw hf he (blaze p)) (pow_nonneg Ξ.awake _) ?_ hc
  unfold f'; simp_rw [← pow_mul]; exact hm.1

omit [FiniteDimensional ℝ E] in
include H in
lemma leaf_bright (M : Leaf R)(ht:X.x=x)(_hp: Clutch X z' o.a R.beta d y j V f' g) (hB : 0≤B)
    (hc:∀ Y Z:Support c,Y⊆ Z → Brush j 1 (B*coverNumber X.B Z) (fun t=> X.enforce (2*o.a) (f' t) (X.plaza Y)) y) :
    Brush j M.weight (B*spanW T R X.B Q.halo (M.turn.badge S)) (fun t=> M.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z'))) y:=by
  have hA' : areas R T 0 X.B (M.turn.badge S) ⊆ H.supportP (M.turn.badge S):=by
    change _⊆ areas R T Q.halo (radiusB x) _
    simp_rw [M.turn.badge_area]; exact Corona.halo_mono (by simp) (Subset.refl _)
  have hM := hc _ _ hA'
  have hh := (Brush.certified (d:=0) (x:=y) (k:=j) (le_refl 0) (M.ingredient (X.input (worldZ X R.beta z')))|>.climb (M.earn _) (le_refl _)).paints hM
  rw [mul_one,zero_add] at hh; apply hh.climb le_rfl
  apply mul_le_mul_of_nonneg_left _ hB; rw [← Daisy.sparkPath]
  change (coverNumber X.B (footprints T R _ (radiusB x) _):ℝ) ≤ 1+(_ + _)
  rw [← show X.B=radiusB x from congr_arg radiusB ht]
  apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact le_add_of_nonneg_right (Nat.cast_nonneg _)

variable {K:Head S→ℝ} {T':ℝ} {k l:ℕ}
omit [FiniteDimensional ℝ E] in
lemma patrons (ht:X.x=x)(hf:X.χ=χ)(hw:X.width=o.K)(he:X.manifest)(p:Molecule S)
    (hA:M.signs S⊆p) (hv : troupe T R Q.halo (radiusB x) p)
    (hF:0≤T') (hp:Prints H (k*j*2) l T') (hB : 0≤B)(hh:0≤b)(hL:0≤L')(hk:∀ i∈p\M.signs S,0≤K i) (hV: Mode V y j v)
    (h:∀ (U:F.Slice G) (z:Air f G),
      let X:= X.wrapY U; let I:= edgesM S (H.unionP p) (radiusB x)
      ∃ (f':E→Directions G f), Clutch X z o.a R.beta d y j V f' (fun i=>course X A R.beta z (V i)) ∧
        Brush j 1 (b*facescale I z^k) (fun i=> scalp I X (V i) R.beta A z) y ∧
        (∀ M'∈M.own, Brush j M'.weight (B*spanW T R X.B Q.halo (M'.turn.badge S)) (fun t=> M'.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z))) y) ∧
       (∀ i∈p\M.signs S, Brush j (K i) (L'*spanW T R X.B Q.halo i) (fun t=> Polar.ember (vary X (V t)) o.a R W Q.table (f' t) (X.input (worldZ X R.beta z)) (course X A R.beta z (V t)) (own p) Q.halo i) y)) :
    let m:=(F.order G).prod X.dice
    ∃ f, Integrable f m ∧ (∫ y,f y ∂m) ≤ ((1+T')*(1+b+2*(L'+B))^j)*M.weight* (∏i∈p\M.signs S,K i)* Ξ.rad^(blaze p).card*(1+H.shapeW p)^(l+j) ∧
          ∀ z, Brush j (f z) 1 (fun t=> M.carat (edgesM S (H.unionP p) (radiusB x)) X (V t) A Q.table p W o.a Q.halo z) y := by
  intro m
  let I:= edgesM S (H.unionP p) (radiusB x); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p)
  let f(z : Air f G):= facescale I z^(k*j); let S':=1+H.shapeW p; let X' z:= J.indicator f z
  let P':=(∏i∈p\M.signs S,K i); let a:=(M.weight*P')*(1+b+2*(L'+B))^j*S'^j
  have ha:0 ≤ a:= by have ht:0≤P':=prod_nonneg hk; have hv:=M.profit; have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p); unfold a; positivity
  obtain ⟨hf',hE⟩:= dries X H Ξ ht hf hw he p (k*j) l T' hF hp
  have hhP: Integrable (fun z:F.Slice G × Air _ G=> a*X' z.snd) m := (hf'.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]; dsimp only; simp_rw [integral_const_mul]; rw [integral_const]
    simp only [probReal_univ,one_smul]; apply (mul_le_mul_of_nonneg_left hE ha).trans
    unfold a S' P'; apply le_of_eq; ring
  intro ⟨v',z⟩
  obtain ⟨f',hg,hq,hD,hC⟩:= h v' z
  apply (measures (z':=z) M (X.wrapY v') H hv hA Ξ.clock ht hw he hV hg hB hL hD hC hq hh).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    -- wrapY and X? maybe defeq
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
end YM.RemainderComparison.Cascade
