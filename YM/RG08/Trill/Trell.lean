import YM.RG08.Trill.Opal
/-! # Mark read: SymReal tensor currency and actual label coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Trill
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius
variable {G:Gauge}{d n p l e D k:ℕ}{σ B:ℝ}
local notation "E"=>Ed G Cover
local notation "Y"=>Snap G d
abbrev Harp (G:Gauge)(d p:ℕ):=Tensor.T (Snap G d) ℝ p
/-- consistent extension off Labels; later on inputs satisfying global color at their own rank, only
  values on Label (no projection/invariant formed externally). Useful off-space to measure correlated
  output terms before showing invariance of full step. -/
def seatMap (U:Labels.Frame G d): Pol G→ₗ[ℂ] U.Coeff:=U.coords.toLinearMap.comp (localFields G d).subtype.leftInverse
lemma seatMap_read (U:Labels.Frame G d)(Q:Label G d): seatMap U Q.val=U.coords Q:=by
 unfold seatMap; rw [LinearMap.comp_apply];change U.coords ((localFields G d).subtype.leftInverse ((localFields G d).subtype Q))=U.coords Q;rw [LinearMap.leftInverse_apply_of_inj (Submodule.ker_subtype _)]

def paintBand (M:Harp G d p): Tensor.T Y ℂ p:=Complex.ofRealCLM.compContinuousMultilinearMap M
lemma tintBand (M:Harp G d p)(x:Fin p→Y):paintBand M x=(M x:ℝ):=rfl
def pointT (x:Fin p→Y):Harp G d p→ₗ[ℝ]ℝ where
 toFun M:=M x
 map_add' _ _:=rfl
 map_smul' _ _:=rfl

def canvas (G:Gauge)(d p k:ℕ):Harp G d p→ₗ[ℝ] Pol G:=
 ∑ x:Fin p→Board G d with depth x=k,
 LinearMap.smulRight (pointT (chip ∘ x)) (∏ a:Fin p,MvPolynomial.X (R:=ℂ) (key (x a)))
lemma canvasTile (M:Harp G d p):canvas G d p k M=tile (paintBand M) k:=by
 unfold canvas tile; rw [LinearMap.sum_apply];apply sum_congr rfl;intro i hi
 rw [LinearMap.smulRight_apply];change (M _ :ℝ) • _=C (↑(M _):ℂ) * _
 rw [← IsScalarTower.algebraMap_smul ℂ (M (chip ∘ i)),MvPolynomial.smul_eq_C_mul];rfl

def tally (U:Labels.Frame G d)(p k:ℕ)(i:U.Index):Harp G d p→ₗ[ℝ]ℝ:=Complex.reCLM.toLinearMap.comp ((LinearMap.proj (φ:=fun _:U.Index=>ℂ) i).comp (((seatMap U).restrictScalars ℝ).comp (canvas G d p k)))
lemma tally_use (U:Labels.Frame G d)(M:Harp G d p)(i:U.Index):tally U p k i M = (seatMap U (tile (paintBand M) k) i).re:= by
 change (seatMap U (canvas G d p k M) i).re=_;rw [canvasTile]
-- calibration also when supplies only constant colors & engineering horizons
lemma canvasBar (M:Harp G d p):conjPol (canvas G d p k M)=canvas G d p k M:=by
 rw [canvasTile]; unfold conjPol
 -- map maps
 unfold tile;rw [map_sum];apply sum_congr rfl;intro x _;rw [_root_.map_mul,map_prod]; simp [paintBand]
lemma spanBar (_U:Labels.Frame G d)(M:Harp G d p){Q:Label G d}(he:Q.val=tile (paintBand M) k):realBar Q=Q:=by apply Subtype.ext; change conjPol Q.val=Q.val;rw [he,←canvasTile,canvasBar]
lemma tally_label (U:Labels.Frame G d)(M:Harp G d p){Q:Label G d}(he:Q.val=tile (paintBand M) k)(i:U.Index): (↑(tally U p k i M):ℂ)=U.coords Q i:=by
 rw [tally_use,←he,seatMap_read];have hv:= U.conj_basis (U.coords Q) i; rw [U.coords.symm_apply_apply,spanBar U M he] at hv
 have hz:=congrArg Complex.im hv
 rw [Complex.star_def,Complex.conj_im] at hz
 apply Complex.ext; simp; simp; linarith

def harrow (F:Gras G n)(f:Pearl)(p d:ℕ):Harp G d p:=Tensor.coeff (grants F f p d) p 0
variable {F:Gras G n}{g:0<σ}
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 600000
lemma harrow_diag (he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl)(X:Y): Tensor.diagonal (harrow F f p d) X=grants F f p d X:=by
 have hf : ContDiffAt ℝ p (grants F f p d) 0 := (grants_smooth he hh hb f).contDiffAt.of_le le_top
 unfold harrow;rw [← leading_tensor X _ hf];simp_rw [grants_scale];rw [lead_monomial,if_pos rfl]
lemma harrow_sym (he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl) : Tensor.Sym (harrow F f p d):=Tensor.coeff_symm ((grants_smooth he hh hb f).contDiffAt.of_le le_top)
lemma paint_synth (he:Lyrics F)(hh:Sings (stance _) D g F B)(hb:0≤B)(f:Pearl): Tensor.coeff (synth F f p d) p 0=paintBand (harrow F f p d):=by
 change Tensor.coeff (Complex.ofRealCLM ∘ grants F f p d) p 0=_;unfold Tensor.coeff;ext1 v
 rw [Complex.ofRealCLM.iteratedFDeriv_comp_left ((grants_smooth he hh hb f).contDiffAt) (i:=p) (show (p:WithTop ℕ∞)≤ω from le_top)]
 change (p.factorial:ℝ)⁻¹ • Complex.ofRealCLM _=Complex.ofRealCLM ((p.factorial:ℝ)⁻¹ • _);rw [_root_.map_smul]
variable {P:GrainS (Ed G Cover)}
def stocked (hc:Calls l P)(hp:Permit D l P)(H:Hol G)(f:Pearl)(e n p d:ℕ):Label G d:= archive (synth_safe (p:=p) (d:=d) (e:=e) (n:=n) hc hp H f)
lemma harrow_tile (hc:Calls l P)(hp:Permit D l P)(H:Hol G)(f:Pearl)(hk:k≤d)(hl:p≤d) : (gradePart (k,p) (stocked hc hp H f e n p d)).val=tile (paintBand (harrow (P e n) f p d)) k:=by
 rw [stocked,Parts.capture _ hk hl]
 obtain ⟨_,hs,C,hC,hT⟩:=(hp.price e n).2
 rw [paint_synth (hp.price e n).1 hT hC]
lemma grades_two (U:Labels.Frame G d)(i:U.Index):(U.grades i).2≤(U.grades i).1:=by
 have he:(U.basis i).val≠0:=fun h=>U.basis.ne_zero i (Subtype.ext h)
 obtain ⟨s,hs⟩:= Finset.nonempty_iff_ne_empty.mpr (show ((U.basis i).val.support)≠∅ from by simpa using he)
 have hz:=(pure_grade (U.grades i) (U.basis i)).mp (U.pure i) (MvPolynomial.mem_support_iff.mp hs)
 have ht:=power_le s; rw [hz] at ht;exact ht.trans_eq (congrArg Prod.fst ((weight_slot s).symm.trans hz))
lemma used (U:Labels.Frame G d)(hc:Calls l P)(hp:Permit D l P)(H:Hol G)(f:Pearl)(i:U.Index)(e n:ℕ):
 let r:=(U.grades i).2
 let k:=(U.grades i).1
 (↑(tally U r k i (harrow (P e n) f r d)):ℂ)=U.coords (stocked hc hp H f e n r d) i:=by
 intro r k
 rw [tally_label U _ (harrow_tile hc hp H f (U.bound i) ((grades_two U i).trans (U.bound i)))]
 let S := stocked hc hp H f e n r d
 change U.coords (gradePart (U.grades i) S) i = U.coords S i
 rw [← U.basis.sum_repr S]
 simp only [map_sum, Finset.sum_apply, _root_.map_smul, Pi.smul_apply]
 apply Finset.sum_congr rfl
 intro j _
 by_cases h : U.grades i = U.grades j
 · rw [h, gradePart_self _ _ (U.pure j)]
 · have hij : i ≠ j := fun e => h (e ▸ rfl)
   simp only [gradePart_zero _ _ _ h (U.pure j), map_zero, Pi.zero_apply,
     Labels.Frame.coords_basis, Pi.single_eq_of_ne hij]
end YM.RG08.Trill
