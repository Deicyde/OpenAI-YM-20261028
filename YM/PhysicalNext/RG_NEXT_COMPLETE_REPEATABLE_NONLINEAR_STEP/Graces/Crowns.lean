import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Aspire
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Optics
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Citrus

/-!
 # Ready λ crown payroll across all.Shape & nonwrapping. Small supplied with extra glider billed independently, not for forecast tests.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{s:Sheet G}{K:MapPrices}
variable (C:Programs s) (r : ℕ→ℕ→ℕ) (b j i n d: ℕ)
section an
variable (P:Stage) (M K:ℝ)
-- exact tweak P fee per polar.LIGHT.With.N.Parameters.Ppre.Minimum

def winG (G:Gauge)(P:Stage)(d:ℕ)(L:Side):= coinFee G P d L / (2 * (L.val:ℝ)^d)
lemma stirs (G:Gauge)(L:Side):0<winG G P d L:=div_pos (coin_pos G P d L) (by positivity)
lemma startsG (G:Gauge)(p:Stage)(_h:1 ≤ M) : ∀ᶠ x:ℕ in atTop,∀ L:Side,L.val=x→ M*(L.val:ℝ)⁻¹^(b+1) ≤ winG G p b L / 2:=by
   let s:= host G p b; have hs:0<s:= simpleH ..
   filter_upwards [((tendsto_rpow_atTop (by norm_num: (0:ℝ)<3/5)).comp (tendsto_natCast_atTop_atTop)).eventually_ge_atTop (4*s*M)] with x hx L hV
   unfold winG coinFee rate; let z:=(L.val:ℝ); have hz:0<z:= Nat.cast_pos.mpr L.property
   change M*z⁻¹^(b+1) ≤ z^(-(2/5:ℝ))/s/(2*z^b)/2
   have hh : z^(3/5:ℝ)= z*z ^ (-(2/5:ℝ)):=by rw [show (3/5:ℝ)=1+-(2/5:ℝ) by ring,Real.rpow_add hz,Real.rpow_one]
   have hc : 4*s*M≤z*z^ (-(2/5:ℝ)):=hh ▸ (show 4*s*M≤z^(3/5:ℝ) from (by change _≤ ((↑x:ℝ)^(3/5:ℝ)) at hx; unfold z; rw [hV]; exact hx))
   rw [pow_succ, inv_pow]; field_simp [hs.ne']; nlinarith only [mul_le_mul_of_nonneg_right hc (pow_nonneg hz.le b),hc] -- edit
end an

def goodD (s: Sheet G)(j i d : ℕ): Prop:=StepStages j i ∧ d+1≤(s.profile i).order∧d≤(s.profile j).power∧d+2≤j

def oldP (C:Programs s) (K:MapPrices) (r : ℕ→ℕ→ℕ) (j i d:ℕ) (L:Side) := let A:=s.profile j; let B:=s.profile i; let V:=C j i; let k:=r j i
    let Y:= winG G B d L; let q:=B.supportExponent+2
    Release.accepts k A.supportExponent q L ∧ ∃ M P P':ℝ,
      1 ≤ M ∧ 1≤P∧1≤P'∧ priceA B.power d k A.supportExponent q M P V.rights∧priceB B.power d k A.supportExponent q P' V ∧
      P*(L.val:ℝ)⁻¹^(d+1) ≤ Y/2 ∧ P'*(L.val:ℝ)⁻¹^(d+1) ≤ Y/2 ∧
        ∀ (c f:Side)(S:StepData c f)(T:Tube G S), (query s K j i).Funds S T→ Peak.glider G T d A.power (2*V.C) M

def Moms (C:Programs s)(K : MapPrices)(r:ℕ→ℕ→ℕ)(L:ℕ→ℕ) := ∀ j i d, goodD s j i d →∀ f:Side,L j ≤ f.val→ oldP C K r j i d f
lemma aspirations (K:MapPrices) (hq:goodD s j i d): ∀ᶠ x:ℕ in atTop, ∀ f:Side,f.val=x→ oldP C K r j i d f:=by
   let P:=query s K j i; let V:=C j i; let A:=s.profile i; let B:=s.profile j
   let a:=A.supportExponent+2; have he:0<a:= add_pos A.price_pos (by norm_num)
   have ht:0<2*V.C:=by have hi:=V.C_one; positivity
   obtain ⟨M,hM,hF⟩:= Peak.cradle G d B.power (2*V.C) P.C ht hq.2.2.1 P.width
   obtain ⟨Z,hZ,hΨ⟩:= gestureA V.rights d A.power (r j i) M (by linarith : 0≤ M) B.price_pos he.le
   obtain ⟨E,hE,hΞ⟩:= foggy V d A.power (r j i) B.price_pos he.le
   filter_upwards [startsG d Z G A hZ, startsG d E G A hE, (tendsto_natCast_atTop_atTop.atTop_mul_const B.price_pos).eventually_ge_atTop (20* Release.base a (r j i))] with x h z u f hf
   refine ⟨(by unfold Release.accepts; rw [hf]; exact u),M,Z,E,hM,hZ,hE,(fun c f=>hΨ), (fun c f=>hΞ), h f hf,z f hf,fun c f S T H=>hF S T (fun l hl=> ?_)⟩
   exact (H.crosses.2.2.2 l (show l.length≤P.j-2 from (let ht : d+2 ≤ j := hq.2.2.2; show l.length ≤ j-2 from by omega))).1
lemma correspond (K : MapPrices) : ∃ L:ℕ→ℕ, Moms C K r L:=by
   obtain ⟨M,-,-,H⟩:= collect_upper s.floorL (fun j x=>∀ i, StepStages j i→ ∀ d∈Finset.range j, goodD s j i d→∀ f:Side,f.val=x→ oldP C K r j i d f) fun j=> eventually_transitions j _ (fun i x=> ∀ d∈Finset.range j,goodD s j i d →∀ f:Side,f.val=x→ oldP C K r j i d f) (fun i he=> (Finset.range j).eventually_all.mpr (fun d _=> by
    by_cases hf:goodD s j i d
    · filter_upwards [aspirations C r j i d K hf] with x hP h; exact (hP : ∀ f:Side, f.val=x→ oldP C K r j i d f)
    exact Eventually.of_forall fun x (h:goodD s j i d) (f:Side)(hf':f.val=x)=>False.elim (hf h)))
   refine ⟨M, fun j i d hi f hf=> H _ f.val hf i hi.1 _ (mem_range.mpr (by have hx:=hi.2.2.2; omega)) hi f rfl⟩
end YM.PhysicalNext.Repeat.Graces
