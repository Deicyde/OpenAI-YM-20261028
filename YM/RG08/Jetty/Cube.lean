import YM.RG08.Jetty.Down
import YM.Space.Configurations
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exponentially weighted test presentations

Span nonlinear functions of polynomial growth, in particular ALL Taylor
polys on unbounded E4 addresses and smooth compact supports. ∞ as in
TestFunction on this observable branch. **ordered** partials, no factorial,
so Taylor displacements pay factorials in receipts explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open scoped Topology ContDiff BigOperators Classical
open Function MeasureTheory Set Filter Topology

def pearl : Submodule ℝ (E4→ℝ) where
 carrier := setOf HasTemperateGrowth
 zero_mem' := HasTemperateGrowth.zero
 add_mem' := HasTemperateGrowth.add
 smul_mem' c x h:= show HasTemperateGrowth ((fun _:E4=>c) • x) from (HasTemperateGrowth.const c).smul h
abbrev Pearl := ↥pearl
theorem Pearl.smooth (f:Pearl) : ContDiff ℝ ∞ f.val:=(show HasTemperateGrowth f.val from f.property).1
theorem Pearl.order (f:Pearl)(n:ℕ): ContDiff ℝ n f.val:= contDiff_infty.mp f.smooth n

abbrev Cargo (n:ℕ):= Fin n→Axis
abbrev Jet (d:ℕ):= Σ i:Fin (d+1),Cargo i.val
variable {n d:ℕ}
def loot (s:Cargo n)(x:E4):Pearl→ₗ[ℝ] ℝ where
 toFun f:= iteratedFDeriv ℝ n f.val x (basis ∘ s)
 map_add' f g:= by
   change iteratedFDeriv ℝ n (f.val+g.val) x _ =_+_
   rw [iteratedFDeriv_add (f.order _) (g.order _)];rfl
 map_smul' c f:=by
   change iteratedFDeriv ℝ n (c • f.val) x _ =_
   rw [iteratedFDeriv_const_smul_apply ((f.order _).contDiffAt)];rfl
def openJet (i:Jet d)(x:E4)(f:Pearl):ℝ:= loot i.2 x f

def warp (σ r:ℝ):= Real.exp (- (σ*r))
lemma warp_pos (σ r:ℝ): 0 < warp σ r:= Real.exp_pos _

lemma cool (k:ℕ){σ:ℝ}(h:0<σ) : Tendsto (fun r=> (1+r)^k * warp σ r) atTop (𝓝 0):=by
 have he:= (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (show Tendsto (fun x:ℝ=>σ*(1+x)) atTop atTop from ((tendsto_atTop_add_const_left atTop (1:ℝ) (tendsto_id (α:=ℝ)))|>.const_mul_atTop h)) -- edit
 have ht := he.mul_const (Real.exp σ / σ^k)
 rw [zero_mul] at ht
 apply Tendsto.congr (fun r=>?_) ht
 change (σ*(1+r))^k * Real.exp _ * (_/_)=_
 unfold warp
 rw [show -(σ*(1+r))=-σ+- (σ*r) by ring, Real.exp_add, Real.exp_neg σ, mul_pow]
 field_simp [h.ne',(Real.exp_pos σ).ne']

lemma cold (k:ℕ){σ:ℝ}(h:0<σ):∃ C:ℝ,0≤C∧∀ r,0≤r→(1+r)^k*warp σ r≤ C:=by
 obtain ⟨b,hb⟩:= eventually_atTop.mp ((cool k h).eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)))
 let B:=max 0 b
 have he:0≤B:=le_max_left ..
 refine ⟨(1+B)^k+1,by positivity,fun r hr=>?_⟩
 rcases le_total B r with hs|hs
 · exact (hb _ ((le_max_right ..).trans hs)).trans (le_add_of_nonneg_left (by positivity))
 have hz:warp σ r ≤ 1:= Real.exp_le_one_iff.mpr (by linarith [mul_nonneg h.le hr])
 exact (mul_le_of_le_one_right (pow_nonneg (by linarith) _) hz).trans ((pow_le_pow_left₀ (by linarith only [hr]:0≤1+r) (by linarith only [hs]) _).trans (le_add_of_nonneg_right zero_le_one))

@[fun_prop] lemma opens (f:Pearl)(s:Jet d):Continuous fun x=>openJet s x f:=by
 have ht:= (f.order s.1.val).continuous_iteratedFDeriv (m:=s.1.val) le_rfl
 exact ((ContinuousMultilinearMap.apply ℝ (fun _=>E4) ℝ (basis ∘ s.2)).continuous.comp ht)
lemma opens_le (f:Pearl)(s:Jet d)(x:E4) :|openJet s x f|≤ ‖iteratedFDeriv ℝ s.1.val f.val x‖:=by
 have he:= (iteratedFDeriv ℝ s.1.val f.val x).le_opNorm (basis ∘ s.2)
 simpa [openJet,loot,Real.norm_eq_abs] using he
lemma rosette (f:Pearl)(d:ℕ):∃ k:ℕ,∃ C:ℝ,0≤C∧∀ (s:Jet d)(x:E4),|openJet s x f|≤ C*(1+‖x‖)^k:=by
 obtain ⟨k,C,hK,he⟩:= HasTemperateGrowth.norm_iteratedFDeriv_le_uniform f.property d
 exact ⟨k,C,hK,fun s x=> (opens_le f s x).trans (he s.1.val (by have h:=s.1.isLt;omega) x)⟩

private def jewel (s:Jet d)(σ:ℝ)(f:Pearl):C(E4,ℝ):= ⟨fun x=> openJet s x f * warp σ ‖x‖,(opens f s).mul (by unfold warp; fun_prop)⟩
variable {σ:ℝ}
private lemma gild (s:Jet d)(f:Pearl)(h:0<σ): Tendsto (jewel s σ f) (coclosedCompact E4) (𝓝 0):=by
 obtain ⟨k,C,hC,hF⟩:= rosette f d
 rw [coclosedCompact_eq_cocompact]
 refine squeeze_zero_norm' (a:=fun x=> C*((1+‖x‖)^k * warp σ ‖x‖)) (Eventually.of_forall (fun x=>?_)) ?_
 · change ‖openJet s x f * _‖ ≤ _
   rw [Real.norm_eq_abs,abs_mul,abs_of_pos (warp_pos ..),← mul_assoc]
   exact mul_le_mul_of_nonneg_right (hF ..) (warp_pos ..).le
 replace ht:= (cool k h).const_mul C
 rw [mul_zero] at ht; exact ht.comp (tendsto_norm_cocompact_atTop (E:=E4))
def gleam (d:ℕ)(h:0<σ):Pearl→ₗ[ℝ] Cloud E4 (Jet d) where
 toFun f s:= raised (jewel s σ f) (gild s f h)
 map_add' f g:= by
   ext s p; induction p using OnePoint.rec
   · change (0:ℝ)=0+0;ring
   · rename_i x; change openJet s x (f+g)*_=_+_; unfold openJet; rw [map_add,add_mul]; rfl
 map_smul' a f:= by
    ext s p; induction p using OnePoint.rec
    · change (0:ℝ)=a*0;ring
    · rename_i x; change openJet s x (a • f)*_=a*(openJet s x f*_);unfold openJet; rw [map_smul,smul_eq_mul]; ring
lemma gleam_at (f:Pearl)(h:0<σ)(s:Jet d)(x:E4): gleam d h f s (push E4 x)=openJet s x f*warp σ ‖x‖:=rfl
lemma shine (h:0<σ)(f:Pearl)(s:Jet d): gleam d h f s OnePoint.infty=0:=rfl

def first (d:ℕ):Jet d:= ⟨0,Fin.elim0⟩
lemma first_open (d:ℕ)(f:Pearl)(x:E4):openJet (first d) x f=f.val x:=by change iteratedFDeriv ℝ 0 f.val x (basis ∘ (first d).2) = _;rw [iteratedFDeriv_zero_apply]
lemma gleaming (h:0<σ):Injective (gleam d h):=by
 intro f g he; apply Subtype.ext; funext x
 have hx:=congrArg (fun z:Cloud E4 (Jet d)=>z (first d) (push _ x)) he
 simp_rw [gleam_at,first_open] at hx
 exact mul_right_cancel₀ (warp_pos ..).ne' hx
end YM.RG08.Jetty
