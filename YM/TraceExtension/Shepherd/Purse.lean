import YM.TraceExtension.Shepherd.Cage
import YM.Push.STRESS_FLUX.LinkD
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side} (x:Site n)(a: Step)
variable (g:G.El) (P: Support n)
local notation "X"=> Config G n
lemma modify_off (U:X) (hp:x ∉ P): Agrees P U (StressFlux.modify x a g U):=by
    intro l hl hm; by_cases h:l=a.used x; swap; · exact (if_neg h).symm
    subst l; unfold Step.used at hl hm; split at hl <;> simp_all
lemma modify_local {U V:X}(he:Agrees P U V): Agrees P (StressFlux.modify x a g U) (StressFlux.modify x a g V):=by
   intro i hi hj; unfold StressFlux.modify; rw[he i hi hj]
lemma modify_g (z:Site n→ G.El)(U:X) : Lattice.gauge z (StressFlux.modify x a g U)= StressFlux.modify x a (z x * g * (z x)⁻¹) (Lattice.gauge z U):=by
   funext i; unfold StressFlux.modify Lattice.gauge; by_cases hx:i=a.used x
   · subst i; cases e:a.neg<;> simp [Step.used,e]<;>group
   simp [hx]
lemma paint_local (d:ℝ)(ht:G.chord g ≤ d) (U:X)(t:Edge (Site n)): knot (U t) (StressFlux.modify x a g U t) ≤ d:=by
   unfold StressFlux.modify; have hh:= (G.chord_nonneg g).trans ht; split
   next he=> split
             next h=> unfold knot; rw [show U t*(U t*g⁻¹)⁻¹=U t*g*(U t)⁻¹ from by group, G.chord_conj]; exact ht
             next h=> unfold knot;rw [show U t*(g*U t)⁻¹=g⁻¹ from by group,G.chord_inv];exact ht
   simpa[knot] using hh
variable (R:Rep G n)
local notation "t"=> R.p.threshold
set_option maxHeartbeats 400000 in
lemma smallC (d:ℝ)(ht:G.chord g ≤ d)(hd:8*d ≤ R.p.threshold) (U:Config G n)(hh:Healthy (R.p.threshold/4) {x} (StressFlux.modify x a g U)):
    flags R.p.threshold U=flags R.p.threshold (StressFlux.modify x a g U)∧ Brink R d U (StressFlux.modify x a g U):=by
   let V:= StressFlux.modify x a g U; let c:=(R.p.threshold)
   let f(F:Face (Per n))(U:X):= G.chord (faceValue U F)
   have hq:= paint_local x a g d ht U; have hp(i:Face (Per n)) (hz:f i U≠ f i V) : f i U ≤ c ∧ f i V ≤ c:=by
      have h : x∈ touched i:= not_not.mp (fun h=> hz (congr_arg G.chord (travel_local _ _ _ _ (fun e hp hv=> modify_off x a g (touched i) U h e (List.mem_toFinset.mpr hp) (List.mem_toFinset.mpr hv)))))
      have hB : f i V ≤ c/4:= le_of_not_gt fun he=> disjoint_left.mp hh (mem_singleton_self _) ((flags_spec ..).mpr ⟨i,h,he⟩)
      have hm : |f i U-f i V|≤ 4*d:= (castC ..).trans (by simpa only [faceValue,square,List.length_cons,List.length_nil,Nat.cast_ofNat] using! hike U V hq i.1 (square i.2.val.1 i.2.val.2))
      refine ⟨?_,?_⟩; all_goals linarith only[show 0<c from R.p.threshold_pos,hB,le_abs_self (f i U-f i V),hm,show 8*d≤ c from hd]
   have hz(i:Face (Per n)): R.p.threshold < f i U ↔ R.p.threshold < f i V:=by by_cases h:f i U=f i V; rw [h]; exact iff_of_false (not_lt.mpr (hp i h).1) (not_lt.mpr (hp i h).2)
   have hx(s:Seat n)(p:Face (Per n))(he:f p (s.view U)≠f p (s.view V)): f p (s.view U) ≤ c ∧ f p (s.view V)≤ c:=by
       have hv(U:X):f p (s.view U)= f (Face.send s.1 s.2 p) U:= Face.send_price (R:=Per n) (K:=G.El) (M:=ℝ) U p s.1 s.2 G.chord G.chord_inv (fun k g=> G.chord_conj g k)
       rw[hv,hv] at he ⊢; exact hp _ he
   refine ⟨?_,⟨(G.chord_nonneg _).trans ht,fun s e=> ?_,fun s=> ?_,fun s p=> hx s _⟩⟩
   · ext p; rw[flags_spec,flags_spec]; exact exists_congr fun i=> and_congr_right fun _=> hz i
   · unfold Seat.view pull Step.read; split; rw[spun]; exact hq _; exact hq _
   unfold kept; apply forall_congr'; intro p; by_cases he:f p (s.view U)=f p (s.view V); unfold f V at he; rw[he]
   have hM : c≤ c*Real.exp ((separation 0 p.1:ℝ)/R.clip.relaxation):= le_mul_of_one_le_right R.p.threshold_pos.le (Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) R.clip.radius_pos.le))
   obtain ⟨h,h'⟩:=hx s p he; exact iff_of_true (h.trans hM) (h'.trans hM)
lemma flowA : Measurable (fun i:G.El × Config G n=> StressFlux.modify x a i.1 i.2):=by refine Continuous.measurable ?_ ; refine continuous_pi fun i=> ?_; unfold StressFlux.modify; split_ifs <;> fun_prop
lemma pull_shift (s:Seat n)(d:Axis)(g:G.El)(U:X):
    Seat.view s (StressFlux.modify (affine s.1 s.2 x) ((posDir d).rotate s.1) g U) = StressFlux.modify x (posDir d) g (Seat.view s U):=by
   let a:= posDir d; let b:= a.rotate s.1; let z:= affine s.1 s.2 x; funext i; by_cases hx:i=a.used x
   · rw [hx]; change b.read (StressFlux.modify z b g U) z = a.read (StressFlux.modify x a g _) x; rw [read_modify,read_modify,if_pos rfl,if_pos rfl]; rfl
   have hq: sendEdge s.1 s.2 i≠ b.used z:= fun h=> hx (sendEdge_injective _ _ h)
   rw [show StressFlux.modify x (posDir d) g (Seat.view s U) i=_ from if_neg hx]; unfold Seat.view pull Step.read; split_ifs; exact congr_arg Inv.inv (if_neg hq); exact if_neg hq
end YM.Trace.Shepherd
