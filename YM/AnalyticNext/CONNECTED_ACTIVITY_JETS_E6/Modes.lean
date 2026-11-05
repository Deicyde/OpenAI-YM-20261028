import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Harmonic
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Schism

/-!
# Portal costs; ready for flat interpolation.

Price one oriented weak spot on all lifted inputs. This version obtains
light and affine-stroke jets; for estimated cores hard-clipped analog still
require `roles`. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Frond
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Scroll Strokes Quill
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {s : ℝ} {P : Teller G} {L : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {j : ℕ} {U : E → Config G f} {V Q : E → Config G c} {x : E} {v z a w b d e : ℝ}
open Brush

lemma grove (p : P.Funds S T) (hL : S.patch.L=L) (hV : Mode V x j v) (t : S.Choices)
    (hQ : Mode (fun i=> S.prediction (replica S.ratio (V i)) t) x j v) (i : Rod c f) (s : ℝ) : let R:=till s; let f:= shadowL P
    let Z y:=replica S.ratio (V y); let _Q i:= S.prediction (Z i) t
    Brush j (f+ maxima P L R) (hikeZ G v R (dimLift P R v)) (fun t'=> Scroll.freely T s (V t') t i) x := by
  intro R f Z Q
  have hs := measures (U:=Z) p hV ⟨hV.pos,recopy _ hV.atLink⟩ hQ R
  apply talents R hs (enCanvas p hs hV hL) ?_ i
  unfold hikeZ; apply le_add_of_nonneg_left; have he := hV.pos; have hu := royalty_ge G; positivity

def squarepot (T : Tube G S) (s : ℝ) (k : S.Choices) (U : Config G f) (V : Config G c) (u : Directions G f) (p : Spot c f) :=
    loft T s U k V true p - ∑ i∈parents p, ‖Scroll.freely T s V k i + straightened T (till s) V u i‖^2/2

def ivy (T : Tube G S) (s : ℝ) (t : S.Choices) (p : Spot c f) (x : ZipP G c f) :=
    squarepot T s t (shaft S x) (increment 1 x.1) x.2 p

lemma scaleRate (P : Teller G) (L : Side) : Rate G L 0 (fun x=> scaleQ P L (till x)) := by
  let f:= shadowL P
  have hm := Rate.const (G:=G) (L:=L) f
  let V x:=maxima P L (till x)
  have hn : Rate G L 0 V := (rateOfs P L (fun _=>f) hm).1
  have ht := (rateOfs P L V hn).1
  have hy := (hm.add hn).mul (hm.add hn); rw [add_zero] at hy
  have hp := hn.mul hn; rw [add_zero] at hp
  unfold scaleQ ldCost octaves
  refine ((((Rate.const _).add (hy.mul_left 2)).add ((Rate.const _).add hy)).add ((Rate.const _).add (Rate.add ?_ ?_))).add hp
  · convert ((hm.mul (((hn.add hn).add hm))).mul_left 2) using 1; ring
  convert ((hm.mul (hm.add ((ht.add ht).add ht))).mul_left 2) using 1; ring

lemma raking (P : Teller G) (L : Side) (v : ℝ) : Rate G L 0 (fun x=> hikeZ G v (till x) (dimLift P (till x) v)) := by
  have he : Rate G L 0 (fun x : ℝ=> (till x:ℝ)) := by
    apply Rate.radius_price.compare; filter_upwards with x; rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)]; gcongr; exact Nat.div_le_self _ _
  unfold hikeZ dimLift
  exact (((he.mul_left 2).mul_right _).mul_right _).add ((((Rate.const 4 |>.add (he.mul_left 2)).mul_right _).add (Rate.const _)).add (Rate.const _))

lemma growth (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) : ∃ r : ℝ, 0<r ∧ r≤1 ∧
    ∃ V : ℝ→ℝ, Rate G L 0 V ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D → S.patch.L=L → Room P S T s →
    ∀ (p : Spot c f) (k : S.Choices) (x : ZipP G c f), ‖x‖≤r → Brush j (V s) 1 (ivy T s k p) x := by
  obtain ⟨C,hC,hV⟩:= bounded_stencils P D hD
  obtain ⟨r,v,hr,hr',hv,hD⟩:= dressed P D hD j
  let w x:= hikeZ G v (till x) (dimLift P (till x) v); let m x:= shadowL P+maxima P L (till x)
  let H x:=scaleQ P L (till x)*(1+feeQ P (till x) v)^j
  let A x:=4*(radiusB x:ℝ)*(v*royalty G); let F x:=m x*(1+w x)^j+C*(royalty G*(1*royalty G))*(1+(A x+1+A x))^j
  refine ⟨r,hr,hr',fun x=> H x+2*((F x*F x)*(1+(1+1))^j),?_ ,?_⟩
  · have hp (e : ℝ→ℝ) (h : Rate G L 0 e) : Rate G L 0 (fun x=> (1+e x)^j) := by simpa only [zero_mul] using!
      (((Rate.const 1).add h).pow j)
    have hh : Rate G L 0 H := by convert (scaleRate P L).mul (hp _ (rateOfs P L (fun _=>v) (Rate.const _)).2) using 1; ring
    have he : Rate G L 0 m := (Rate.const _).add (rateOfs P L (fun _=> shadowL P) (Rate.const _)).1
    have ha : Rate G L 0 A := (Rate.radius_price.mul_left 4).mul_right _
    have hf : Rate G L 0 F := Rate.add (by simpa only [add_zero] using! he.mul (hp _ (raking P L v)))
      ((hp _ ((ha.add (Rate.const 1)).add ha)).mul_left _)
    apply hh.add; convert ((hf.mul hf).mul_right _).mul_left 2 using 1; ring
  filter_upwards with x c f S T hS hL h i k u hu
  obtain ⟨h1,h2,h3,h4,h5⟩:= hD c f S T h.accepted hS u hu k
  have ht : ‖u.2‖ ≤ 1 := (le_max_right ..).trans (show max ‖u.1‖ ‖u.2‖≤1 from hu.trans hr')
  let L' := fun v:ZipP G c f=> increment (1:Config G c) v.1
  apply ((wild (L:=L) h.accepted hL h2 h1 k h4 i x).trim).separating
  let A q (v:ZipP G c f):=Scroll.freely T x (L' v) k q+straightened T (till x) (L' v) v.2 q
  have hz (i:Bond f) : Brush j 1 1 (fun z:ZipP G c f=>z.2 i) u := by
    let a : Directions G f→L[ℝ] G.Color := ContinuousLinearMap.proj i; let b:= a.comp (ContinuousLinearMap.snd ℝ (Directions G c) (Directions G f))
    apply linearB b ((norm_le_pi_norm u.2 i).trans ht) _ zero_le_one
    rw [one_mul]; refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u=>?_)
    rw [one_mul]; exact ((norm_le_pi_norm u.2 i).trans (le_max_right ..) : ‖u.2 i‖≤ _)
  have he q : Brush j (F x) 1 (A q) u := by
    apply ((grove h.accepted hL (show Mode L' u j v from h1) k h5 q x).trim).gathering
    exact (hard_turn q h (u:=Prod.snd) zero_le_one zero_le_one (fun j _=> hz j) h1 (hV _ _ S T hS h.accepted) hC.le).trim
  let Dn := (F x*F x)*(1+(1+1))^j
  have hf j : Brush _ Dn _ _ u := (semi (squared (he j))).trim
  refine (Brush.spree (parents i) (fun q u=> ‖A q u‖^2/2) (fun _=>Dn) zero_le_one (fun i _=> hf i)).climb ?_ le_rfl
  rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ _
  · exact_mod_cast (show (parents i).card ≤ 2 by rcases i with i|i|i <;> simp [parents])
  let p : Rod c f:= .inr (0,0); exact (hf p).nonneg
end YM.ConnectedActivityE6.Blaze.Frond
