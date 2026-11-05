import YM.RemainderComparison.Halo.Cut
import YM.RemainderComparison.Cascade.Main

/-!
 # Scored Gear and price of remaining arches

 All Gear-tested by Brush on actual angles, never differentiating the
 E mask. Use Gear prices only if no hanging vertices are left that could
 charge larger fees; otherwise keep explicit barb.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Raw Itinerary Opacity Cascade
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (H:Cash W x μ L Q o C T R) {q A B b e u v d U' F':ℝ}{j n k:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {V:E→ Config G c} {y:E} {f':E→Directions G f}{z':Air f G}{g:E→Air f G}

namespace Graft

def burn (p:Head S):ℕ:= if ∃ i:WarningAt c f,p=Sum.inr (.inr (.inr i)) then 1 else 0
lemma burn_form (s:Molecule S) : (∑ i∈s,burn i)= (blaze s).card:=by
  unfold burn blaze
  rw [← sum_filter]; simp only [sum_const,nsmul_eq_mul,mul_one]
  symm; exact Finset.card_bij (i:=fun i _=> Sum.inr (Sum.inr (Sum.inr i))) (fun i hi=>mem_filter.mpr ⟨mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi)),⟨i,rfl⟩⟩) (fun _ _ _ _ hx=> Sum.inr.inj (Sum.inr.inj (Sum.inr.inj hx))) (fun a ha=> by obtain ⟨hb,j,rfl⟩:= mem_filter.mp ha; exact ⟨j,mem_toRight.mpr (mem_toRight.mpr (mem_toRight.mpr hb)),rfl⟩)
lemma letter (p:Head S): Ξ.fare p= Ξ.tag p * Ξ.rad^burn p:=by
  have hh:=Ξ.remixes {p}; rw [prod_singleton,prod_singleton,← burn_form,sum_singleton] at hh; exact hh

lemma mix (p:Molecule S)(e:Set ℕ)(w:ℕ→ℝ): (∏ i∈p, weather S e w Ξ.fare i)=(∏ i∈p,weather S e w Ξ.tag i)*Ξ.rad^(blaze p).card:=by
  have he i: weather S e w Ξ.fare i= weather S e w Ξ.tag i*Ξ.rad^burn i:=by
    by_cases h:inherited S e i
    · obtain ⟨i,hi,rfl⟩:= h; rw [weather_at _ hi,weather_at _ hi]
      have hk : burn (Opacity.key S i)=0:=by simp [burn,Opacity.key];
      rw [hk,pow_zero,mul_one]
    unfold weather; rw [dif_neg h,dif_neg h,letter H Ξ i]
  rw [show weather S e w Ξ.fare= _ from funext he,prod_mul_distrib,Finset.prod_pow_eq_pow_sum,burn_form]
-- barb on ALL OTHER vertices; makes the root purchase simpler and does not affect ERA token exponent
lemma barb (s:Molecule S)(e:Set ℕ)(w:ℕ→ℝ) (b:ℝ) : (∏ i∈s, weather S e w (fun i=> b*Ξ.fare i) i) =
    b^((s.filter fun i=> ¬ inherited S e i).card)*(∏ i∈s,weather S e w Ξ.fare i) := by
  let Q i:= weather S e w Ξ.fare i; let Z (p:Head S):= if ¬ inherited S e p then b else 1
  have hh i: weather S e w (fun i=> b*Ξ.fare i) i= Z i*Q i:= by unfold Z Q weather; split_ifs <;> simp [*] at *
  rw [show weather S e w (fun i=> b*Ξ.fare i) = _ from funext hh,prod_mul_distrib]
  unfold Z; rw [← prod_filter,prod_const]
end Graft
structure Graft (H:Cash W x μ L Q o C T R)(Ξ : Utopia H j v d r q χ)(A F B U:ℝ) (k l:ℕ): Prop where
   bark : 0≤B
   plates : 0≤F
   prints : Prints H (k*j*2) l F
   tally : 0≤U
   track (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
      (F: Forest S.ratio) (X:Coat T F) (V:E→ Config G c) (y:E) : let _:=Ξ
      X.χ=χ→X.manifest→X.x=x→X.width=o.K→Mode V y j v→ V y=X.V →∀ z : Air f G,
      ∃ f':E→Directions G f,
       Silica.Clutch X z o.a R.beta d y j V f' (fun i=>course X A R.beta z (V i)) ∧
         (∀ I: Finset (Bond f), Brush j 1 (U*facescale I z^k) (fun i=> scalp I X (V i) R.beta A z) y) ∧
         (∀ Y Z:Support c,Y⊆ Z → Brush j 1 (B*coverNumber X.B Z) (fun t=> X.enforce (2*o.a) (f' t) (X.plaza Y)) y)
namespace Graft
variable (𝓛 : Graft H Ξ A F' B U' k n)

def charge (j:ℕ)(F' U' b:ℝ) := (1+F')*(1+U'+2*b)^j
include 𝓛
lemma grants (hv:0≤b):1 ≤ charge j F' U' b:= by unfold charge; exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right 𝓛.plates) (one_le_pow₀ (by linarith only [𝓛.tally,hv]))

lemma legacy : Heroes H Ξ A (charge j F' U' (r+B)) (n+j) := by
   have hh:=𝓛.bark; have hr:0≤r:=zero_le_one.trans Ξ.active
   intro M p E _ _ _ F X V y hF hM hx hw hP hT hS htM hV he m
   obtain ⟨g,hg,hE,hq⟩:= patrons M X H Ξ hx hF hw hM p htM hT 𝓛.plates 𝓛.prints hh 𝓛.tally hr (fun j _=>Ξ.tagged j) hV (A:=A) (fun U z=> by
    let X:= X.wrapY U
    obtain ⟨f',hp,ha,hF'⟩:= 𝓛.track E F X V y hF hM hx hw hV he z
    refine ⟨_,hp,ha _,fun M _=>leaf_bright X H M hx hp 𝓛.bark hF',fun i hi=>?_⟩
    unfold Utopia.tag; rw [← show X.B=radiusB x from congr_arg radiusB hx]; exact Ξ.stream E F X V _ _ y z hx hw hF hM hV hp (own p) i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP (mem_sdiff.mp hi).1) hP))
   refine ⟨g,hg,hE.trans_eq ?_,hq⟩; unfold charge; rw [Ξ.remixes,keeps_blaze]; ring
variable {C':ℝ}
lemma stratum {E':Set ℕ}{w:ℕ→ℝ}{δ L':ℝ} (p':Molecule S) (h:Presents R E' w δ) (_hz:δ≤1)
   (hc: 0≤ C')
   (hp:∀ (F:Forest S.ratio)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](Z: Coat T F), Z.x=x → ∀ (f':E→Directions G f)(V:E→ Config G c)(U:Config G f)(g:E→ Air f G) (y:E),
    (∀ Y X:Support c,Y⊆ X → Brush j 1 (B*coverNumber Z.B X) (fun t=> Z.enforce (2*o.a) (f' t) (Z.plaza Y)) y) →
      ∀ i∈E', ∀ k:Finset ℕ, Brush j (C'*w i) (B*spanW T R Z.B Q.halo (key S i)) (fun t=> Polar.ember (vary Z (V t)) o.a R W Q.table (f' t) U (g t) k Q.halo (key S i)) y)
   (hB:B≤ L')(hk:∀ i∈ p'\M.signs S, ¬ inherited S E' i→ r ≤ L') :
     Seminar M H p' j A χ (charge j F' U' (L'+B)*M.weight*(∏ i∈p'\M.signs S,weather S E' (fun i=> C'*w i) Ξ.fare i)*(1+H.shapeW p')^(n+j)) v:=by
   have hh:=𝓛.bark; intro E _ _ _ F X U y ht hv hx hX hr hP hY hs hm hU m
   let u':=fun i=> C'*w i; let K:=weather S E' u' Ξ.tag
   obtain ⟨f,hF,hA,hC⟩:= patrons M X H Ξ hx ht hX hv p' hs hP 𝓛.plates 𝓛.prints hh 𝓛.tally (hh.trans hB) (fun i _=>snow_pos Ξ.tagged (fun i _=>mul_nonneg hc (h.pay _)) i) hm (A:=A) (K:=K) (fun Y z=> by
     let Z:= X.wrapY Y
     obtain ⟨f',hg,hZ,hp'⟩:=𝓛.track E F Z U y ht hv hx hX hm hU z
     refine ⟨_,hg,hZ _,fun M _=>leaf_bright Z H M hx hg 𝓛.bark hp',fun i hi=> ?_⟩
     by_cases he:inherited S E' i
     · obtain ⟨i,hi',rfl⟩:= he; unfold K; rw [weather_at _ hi']
       exact (hp F _ Z hx _ U _ _ y hp' i hi' (own p')).climb le_rfl (mul_le_mul_of_nonneg_right hB (spanR Z _))
     unfold K weather; rw [dif_neg he, Utopia.tag, ← show Z.B=radiusB x from congr_arg radiusB hx]; exact (Ξ.stream E F Z U _ _ y z hx hX ht hv hm hg (own p') i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP (mem_sdiff.mp hi).1) hr)).climb le_rfl (mul_le_mul_of_nonneg_right (hk i hi he) (spanR Z i)))
   refine ⟨f,hF,hA.trans_eq ?_,hC⟩; rw [mix,keeps_blaze]; unfold K u' charge; ring
omit 𝓛
lemma tighter {j:ℕ} {A b v:ℝ} {χ:Chi} {p:Molecule S} (hp:Seminar M H p j A χ b v) (he:b≤σ): Seminar M H p j A χ σ v:= by
   intro E _ _ _ F X U y hY hV hx hB hu hP hQ hv hf h m
   obtain ⟨f,h,hp,hF⟩:= hp E F X U y hY hV hx hB hu hP hQ hv hf h
   exact ⟨f,h,hp.trans he,hF⟩
-- statement licensed by stratum & pending
structure Quarry (H:Cash W x μ L Q o C T R) -- edit L shadow
      (Ξ:Utopia H j v d r q χ) (A C' T' B:ℝ) (k:ℕ):Prop where
    ready (M:Team R)(E:Set ℕ)(w:ℕ→ℝ)(δ:ℝ) : Presents R E w δ → δ ≤ 1 → ∀ p:Molecule S,
     Seminar M H p j A χ (B*M.weight*(∏ i∈p\M.signs S,weather S E (fun i=> C'*w i) (fun i=> T'*Ξ.fare i) i)*(1+H.shapeW p)^k) v
variable {T':ℝ}
include 𝓛
lemma acorn
   (hc:0≤ C')(hA:charge j F' U' (r+B+B)≤ T')
   (hp:∀ (F:Forest S.ratio)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](Z: Coat T F), Z.x=x → ∀ (f':E→Directions G f)(V:E→ Config G c)(U:Config G f)(g:E→ Air f G) (y:E) (E':Set ℕ)(w:ℕ→ℝ) (δ:ℝ),
    (∀ Y X:Support c,Y⊆ X → Brush j 1 (B*coverNumber Z.B X) (fun t=> Z.enforce (2*o.a) (f' t) (Z.plaza Y)) y) → Presents R E' w δ → δ ≤ 1 →
      ∀ i∈E', ∀ k:Finset ℕ, Brush j (C'*w i) (B*spanW T R Z.B Q.halo (key S i)) (fun t=> Polar.ember (vary Z (V t)) o.a R W Q.table (f' t) U (g t) k Q.halo (key S i)) y) :
   Quarry H Ξ A C' T' (charge j F' U' (B+B)) (n+j):= by
   have hb:= 𝓛.bark; have hr:0≤r:=zero_le_one.trans Ξ.active; have hT := (grants H Ξ 𝓛 (show 0 ≤ r+B+B from by positivity)).trans hA
   have hm:= grants H Ξ 𝓛 (b:=B+B) (by positivity)
   constructor; intro M E' w δ h hz p
   let s:= p\M.signs S; let k:= s.filter fun i=>¬ inherited S E' i; let u':=fun i=> C'*w i
   have h' (F:Forest S.ratio)(E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](Z:Coat T F)(hZ:Z.x=x) f' V U g y hV := hp F E Z hZ f' V U g y E' w δ hV h hz
   by_cases hh:k=∅
   · have he:k.card=0:= card_eq_zero.mpr hh; rw [barb]; change Seminar M H p j A χ (_ * (T'^k.card*_) * _) _; rw [he,pow_zero,one_mul]
     exact stratum M H Ξ 𝓛 p h hz hc h' le_rfl (fun i hi hI=> by have he':i∈k:=mem_filter.mpr ⟨hi,hI⟩; rw [hh] at he'; simp at he')
   rw [barb]
   apply tighter M H (stratum M H Ξ 𝓛 p h hz hc h' (le_add_of_nonneg_left hr) (fun _ _ _=> le_add_of_nonneg_right hb));
   · let t:=(charge j F' U' (B+B)); let z:=charge j F' U' (r+B+B); let Y:= M.weight; let u:=∏ i∈s,weather S E' u' Ξ.fare i
     have ht:0 ≤ u:=prod_nonneg (fun i _=> snow_pos Ξ.fares (fun i _=> mul_nonneg hc (h.pay i)) i)
     have hp : z≤ t*T'^k.card:= hA.trans ((le_self_pow₀ hT (by exact Nat.ne_of_gt (card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)))).trans (le_mul_of_one_le_left (pow_nonneg (zero_le_one.trans hT) _) hm))
     change z*Y*u*_≤ t*Y*(T'^k.card*u)*_; apply mul_le_mul_of_nonneg_right _ (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) _); exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp M.profit) ht).trans_eq (by ring)
end Graft
end YM.RemainderComparison.Halo
