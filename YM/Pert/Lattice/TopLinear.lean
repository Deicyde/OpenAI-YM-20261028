import YM.Pert.Lattice.Readers
/-! Explicit linear plaquette difference stencils, including on cover arrays. -/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Pert.Bare
open Lattice Function Filter Orb Labels
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {j : ℕ}
section algebra
variable {R : Type*} [AddCommGroup R] [One R]

def wideCurl (U : Lattice.Links R G.Color) (x : Four R) (i k : Axis) := U (x,i) + U (x+step i,k)-U (x,k)-U (x+step k,i)

variable (j G) in
def wideCore (x : Four R) : Lattice.Links R G.Color →ₗ[ℝ] Response G j :=
  LinearMap.pi (fun i => LinearMap.pi (fun k => LinearMap.pi (fun γ => (j.factorial:ℝ)⁻¹ • ∑ s : Finset (Fin j),
    let l := stop x (walk γ s)
    let T (e : Edge (Four R)) := LinearMap.proj (R:=ℝ) (φ:=fun _=>G.Color) e
    sign s • (T (l,i)+T (l+step i,k)-T (l,k)-T (l+step k,i)))))
lemma wideCore_apply (x : Four R) (U : Lattice.Links R G.Color) (i k : Axis) (γ : Fin j→Axis) :
   wideCore G j x U i k γ=(j.factorial:ℝ)⁻¹ • ∑ s, sign s • wideCurl U (x+∑ i∈s,step (γ i)) i k := by
  simp only [wideCore,LinearMap.pi_apply, LinearMap.smul_apply,LinearMap.sum_apply, LinearMap.add_apply,LinearMap.sub_apply,LinearMap.proj_apply,displaced,wideCurl]
variable (j G) in
/-- Generic unscaled link array, no periodic quotient. -/
def wideLink (s : Signed) : Lattice.Links R G.Color →ₗ[ℝ] Lattice.Links R G.Color :=
  LinearMap.pi (fun l => let d := (posDir l.2).rotate s
                         (if d.neg then -1 else (1:ℝ)) • LinearMap.proj (d.used (affine s (0 : Four R) l.1)))
lemma wideLink_apply (s : Signed) (U : Lattice.Links R G.Color) (l : Edge (Four R)) :
    wideLink G s U l = (if ((posDir l.2).rotate s).neg then -1 else (1:ℝ)) •
      U (((posDir l.2).rotate s).used (s.act l.1)) := by unfold wideLink; cases he : ((posDir l.2).rotate s).neg <;> simp [affine,he]
variable (j G) in
def wideLinear (h : ℝ) (x : Four R) : Lattice.Links R G.Color →ₗ[ℝ] Labels.Taylor G j :=
  (Fintype.card Signed : ℝ)⁻¹ • ∑ s : Signed, Labels.Taylor.turn s.ortho ∘ₗ ((h^(-(j+2:ℤ)) • radialMap) ∘ₗ (wideCore G j (affine s⁻¹ 0 x)) ∘ₗ wideLink G s)
end algebra

def slope (h : ℝ) (x : Site n) (j : ℕ) : Potential G n →ₗ[ℝ] Labels.Taylor G j := (Fintype.card Signed : ℝ)⁻¹ • ∑ s : Signed, Labels.Taylor.turn s.ortho ∘ₗ topJet h (affine s⁻¹ 0 x) j ∘ₗ rotation s
lemma slope_eq (h : ℝ) (x : Site n) (v : Potential G n) : wideLinear G j h x v.val=slope h x j v := by
  simp only [wideLinear,slope,topJet,LinearMap.smul_apply,LinearMap.sum_apply, LinearMap.comp_apply]
  refine congrArg (fun v : Labels.Taylor G j => (Fintype.card Signed : ℝ)⁻¹ • v) ?_
  refine Finset.sum_congr rfl fun s _ => congrArg (fun u : Labels.Taylor G j => Labels.Taylor.turn s.ortho (h ^ (-(j+2:ℤ)) • u)) (congrArg (fun q : Response G j => radialMap q) ?_)
  funext i k γ; rw [leading_apply, wideCore_apply]; refine congrArg (fun t : G.Color => (j.factorial:ℝ)⁻¹ • t) ?_
  refine Finset.sum_congr rfl (fun z hz => ?_); apply congrArg (fun u : G.Color => sign z • u)
  rw [displaced]; rfl

lemma tensor_jet (h : ℝ) (x : Site n) : fderiv ℝ (fun v : Potential G n => tensorJet h (positiveLinks v) x j) 0 = (slope h x j).toContinuousLinearMap := by
  have hs (s : Signed) : HasFDerivAt (fun v : Potential G n => oval s h (positiveLinks v) x j)
      (Labels.Taylor.turn s.ortho ∘ₗ topJet h (affine s⁻¹ 0 x) j ∘ₗ rotation s).toContinuousLinearMap 0 := by
    simp_rw [oval,←rotation_links]; let R := (rotation (G:=G) (n:=n) s).toContinuousLinearMap
    let L := (Labels.Taylor.turn (G:=G) (j:=j) s.ortho).toContinuousLinearMap
    let F (a : Potential G n) := rawJet h (positiveLinks a) (affine s⁻¹ 0 x) j
    let H := jet_deriv (G:=G) h (affine s⁻¹ 0 x) (j:=j)
    have hd : HasFDerivAt F _ (R 0) := R.map_zero.symm ▸ H
    exact L.hasFDerivAt.comp (f:=fun y => F (R y)) (g:=fun y=>L y) _ (hd.comp (g:=F) (f:=fun u => R u) 0 R.hasFDerivAt)
  have hf := (HasFDerivAt.sum (𝕜:=ℝ) (E:=Potential G n) (F:=Labels.Taylor G j) (x:=0) (u:=Finset.univ) (fun s _ => hs s)).const_smul ((Fintype.card Signed : ℝ)⁻¹)
  unfold tensorJet; rw [show (fun v : Potential G n => (Fintype.card Signed : ℝ)⁻¹ • ∑ s : Signed, oval s h (positiveLinks v) x j) = _ from funext (fun v => show _ = ((Fintype.card Signed:ℝ)⁻¹ • (∑ s : Signed, (fun v : Potential G n => oval s h (positiveLinks v) x j))) v by rw [Pi.smul_apply, Finset.sum_apply])]; rw [hf.fderiv]
  ext1 v; simp [slope]
lemma constant_lex (h : ℝ) (x : Site n) (v : Coords G n) (z : Key G) : PowerSeries.constantCoeff (seriesLex h x v z) = coord (fun j=>slope h x j (expand G n v)) z := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, seriesLex,PowerSeries.coeff_mk,scaleJet,iteratedFDeriv_one_apply]
  let L := Complex.ofRealCLM.comp ((axes G z.1).coord z.2).toContinuousLinearMap
  let U := fun v : Potential G n => tensorJet h (positiveLinks v) x z.1
  have e : datum h x z = L ∘ U := rfl
  have ht := tensor_jet h x (G:=G) (j:=z.1)
  rw [zero_add,e,fderiv_comp _ L.differentiableAt ((tensor_diff (G:=G) h x z.1).differentiableAt (by simp)), ht,L.fderiv]; norm_cast; simp [L,coord]
end YM.Pert.Bare
