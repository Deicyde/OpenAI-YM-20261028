import YM.PertExtension.OrbLaurent
import YM.Bid.Source
import Mathlib.Tactic

/-! Finite-regulator evaluation on actual type of canonical source sections.
Only real polynomial basis columns here; joint tests are still scalar finite
combinations before Gram changes. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 60000
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.PertExtension.Orb.SlotEvaluation
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory RG Supply Labels Source Drops InnerProductSpace
open scoped Matrix.Norms.Frobenius ContDiff Topology Classical BigOperators ENNReal
attribute [local instance] Gauge.frobInner
open Chart Series Series.Radial Series.Tested Bid
variable {G : Gauge}{n : Side}{d : ℕ}
variable {F : Labels.Frame G d}(C : SectionData F)

def coverAt (o : Site n)(x : Dir G n) := expandAt o (representative x)
def fieldAt (i : F.Index)(o : Site n)(v : Config G n) := (C.places (Pi.single i 1) o v).re
def field (s : RG.Slot)(o : Site n)(k : G.ColorIndex)(x : Dir G n) : ℝ:=s.eval (coverAt o x) k

@[simp] lemma zero_links (o : Site n) : coverAt o (0:Dir G n) = 1 := by simp [coverAt];rfl
@[simp] lemma slot_zero (o : Site n) (s : RG.Slot) : s.eval (coverAt o (0:Dir G n))=0:=by
  have ht (w)(x : Cover) :travel (1:CoverConfig G) x w=1:=by
    induction w generalizing x with
    | nil=>rfl
    | cons a w ih=>simp only [travel,ih,mul_one,Step.read];by_cases h:a.neg=true<;>simp [h]
  rw [zero_links]; unfold RG.Slot.eval faceValue;rw [ht (square ..),G.curvature_unit,map_zero]
@[fun_prop] lemma slotContour (s : RG.Slot)(o : Site n) : ContDiff ℝ ∞ (s.eval ∘ coverAt (G:=G) o) := by
  let f := coverAt o (G:=G)
  have h (w)(x): ContDiff ℝ ω (fun y => G.mat (travel (f y) x w)) := by simp_rw [show ∀ y,travel (f y) x w=travel (representative y) (wrap n x+o) w from fun y=> travel_at o (representative y) x w]; exact smooth_walk _ _
  let v : Dir G n → G.El := fun x=>faceValue (f x) (s.offset,s.plaq)
  have hb : ContDiff ℝ ω (fun x=>G.mat (v x)) := h ..
  let g (x) := G.mat (travel (f (x:Dir G n)) 0 s.walk)
  let Q:=LinearMap.toContinuousLinearMap G.projectColor
  let M:=LinearMap.toContinuousLinearMap G.colorMat
  have H : ContDiff ℝ ω (fun x : Dir G n=>G.curvature (v x)) := by
    unfold curvature; simp_rw [G.mat_inv]
    exact Q.contDiff.comp (hb.sub ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp hb) |>.const_smul (1/2:ℝ))
  have hh : s.eval ∘ coverAt (G:=G) o=fun x=>Q (g x*M ((G.curvature (v x)))*star (g x)):= rfl
  rw [hh]; exact Q.contDiff.comp (((h _ _).mul (M.contDiff.comp H)).mul ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (h _ _)))|>.of_le le_top
@[fun_prop] lemma coordinateContour (s : RG.Slot)(o : Site n)(k : G.ColorIndex) : ContDiff ℝ ∞ (field s o k) := by
  convert! (contDiff_const (c:=EuclideanSpace.basisFun G.ColorIndex ℝ k)).inner ℝ (slotContour s o (G:=G)) using 1
  funext x
  exact (EuclideanSpace.basisFun_inner ..).symm
lemma slotOrder (s : RG.Slot)(o : Site n)(k : G.ColorIndex) : RadialOrder 1 (field s o k) := zero_first (coordinateContour ..).contDiffAt (by unfold field; rw [slot_zero];rfl)

-- representation by source path slots instead of arbitrary polynomial coordinates
lemma repr {i : F.Index} {m : ℕ} (p:Pose G m)(B:Fin m→RG.Slot) (h:C.evaluate (Pi.single i 1)=lumin p ∘ mapped B) (o : Site n) (u : Dir G n) :
   restrictedO (fieldAt C i o) (expLinks G _ u)= (∑ d∈p.support,(MvPolynomial.coeff d p) * ∏ r∈d.support, (Complex.ofReal (field (B r.1) o r.2 u))^(d r)).re := by
 change (C.evaluate _ (coverAt o u)).re = _
 rw [h, Function.comp_apply, Bid.lumin, MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
 rfl

lemma poly_smooth {i : F.Index} {m : ℕ} (p : Pose G m)(B : Fin m → RG.Slot)(h : C.evaluate (Pi.single i 1)=lumin p ∘ mapped B)(o : Site n):
    ContDiff ℝ ∞ (restrictedO (fieldAt C i o) ∘ expLinks G (Cotree n)):=by
  change ContDiff ℝ ∞ fun u=>restrictedO (fieldAt C i o) (expLinks G _ u)
  simp_rw [repr C p B h]
  exact Complex.reCLM.contDiff.comp (.sum fun d _=> contDiff_const.mul <| contDiff_prod fun i _=>
        (Complex.ofRealCLM.contDiff.comp (coordinateContour (B i.1) o i.2)).pow ..)
lemma poly_order {m : ℕ}(p : Pose G m){k : ℕ}(hp : lows p k)(B : Fin m→RG.Slot)(o : Site n)(x : Dir G n):
    Bill k (fun t : ℝ => ∑ d∈p.support, (MvPolynomial.coeff d p) * ∏ i∈d.support, Complex.ofReal (field (B i.1) o i.2 (t • x)) ^ (d i)) := by
  let f : (Fin m × G.ColorIndex) → ℝ → ℂ := fun i t=> Complex.ofReal (field (B i.1) o i.2 (t • x))
  suffices h : Bill k (∑ d∈p.support, (fun t =>MvPolynomial.coeff d p*( (∏ i∈d.support, f i ^ (d i)) t))) by
    convert h using 1
    funext t; simp [Finset.sum_apply, Finset.prod_apply,f]
  apply bill_sum
  intro j hj
  have h (i): Bill 1 (f i) := by
     obtain ⟨C,hC,he⟩ := slotOrder (B i.1) o i.2 x
     refine ⟨C,hC,he.mono fun t ht=>by simpa [f] using! ht⟩
  have hs := bill_product j.support (fun i=>j i*1) _ (fun i _ => bill_pow (h i) (j i))
  refine bill_ge (bill_mul (bill_const (MvPolynomial.coeff j p)) hs) ?_
  simpa [Finsupp.sum] using hp _ hj

lemma pre_field {Hol : Hol G}(h : C.Sound Hol)(s : Bid.pop C)(i : F.Index)(o : Site n) :
    PreTest (fieldAt C i o) ∧ RadialOrder (F.grades i).2 (restrictedO (fieldAt C i o) ∘ expLinks G (Cotree n)) := by
  have hc:= Complex.continuous_re.comp (C.continuous_places (Pi.single i 1) o)
  obtain ⟨m,B,hS,p,hp,hq⟩:= s i
  refine ⟨⟨fun u _ x=>by unfold fieldAt;rw [C.placed_invariant h], ⟨hc.comp continuous_links,(poly_smooth C p B hp _).contDiffAt⟩,hc⟩,fun x=>?_⟩
  obtain ⟨r,hr,H⟩:=poly_order p hq B o x
  refine ⟨r,hr,H.mono fun t ht=> le_trans ?_ ht⟩
  dsimp only [Function.comp_apply]; rw [repr C p B hp,Real.norm_eq_abs];apply Complex.abs_re_le_norm

end YM.PertExtension.Orb.SlotEvaluation
