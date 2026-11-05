import YM.AnalyticNext.QUARTIC_MATCH.Range
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Divisors
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Spectrum


/-!
# Supply TRUE critical station comparisons on auxiliary lattices
of the prescribed small test sizes. Can use any higher-order
input `Supply` here (same Stage in Q, new higher-order uniform service
still movable at the same data, prove by uniqueness at the germ).
Here κ frame unrestricted. Γ slope/sign only charged at this stage.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Pane
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Set
open Further.PhysicalPeriodLimitF933 Gauge Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Matrix Finset
open Push Push.Uniform Shingle Pitch Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {A : Levels G} {D : Horizon A} {O : ChartRatio G} (K : Kin D O)
variable {s : Sheet G} {R : Rolls s} {P : PostCost R}
    (M : K.Planned P) (ho : LocalRatio O) (hA : AsDivisors A.S)
    {N m : ℕ} (Q : Paintings.Supply G (A.clock.op m 0).patch A.clock.kernel (A.params (m+1))) (hm : m<N) {c f : Side} (H : f.val=c.val*(A.S.block m).val)
    (t : Forest (again A m c f H).ratio)
-- scope .Larger at aux; physical period then no-choice variation.
include hA M hm ho
lemma ligatures (ht : 2 ≤ c.val) (he : Larger (G:=G) (again A m c f H)) :
    let V:= again A m c f H; let u:= K.path N (m+1); let v:= K.path N m; let W:=A.params (m+1); let j:=A.clock.J (m+1)
    ∃ ρ : Dir G c→AxisChart G t,
      Q.h.Service (S:=V) t W.clip u ρ ∧ ClassicalMatch (S:=V) t W.clip (A.params m).clip u v ρ ∧
        0<Q.sights ∧ FiniteBound (S:=V) t u v W.clip (A.params m).clip (K.alpha N m) O ρ (Q.allowance+P.Γ j) (min Q.sights (P.c j)) (A.clock.loopCap (m+1)) := by
  intro V u v W j; let L:=A.S.block m
  have hk:=M.cap N (m+1) hm
  obtain ⟨p,-,hp⟩:= hA c 0; let C:= A.S.side m p; let F:= A.S.side (m+1) p
  have hh : c.val ∣ C.val := dvd_mul_of_dvd_left hp _
  obtain ⟨n,hn⟩:= hh
  have hL := M.cap N m hm.le
  let Γ := (A.clock.op m 0).patch; let Z:= A.clock.kernel
  have hV : f.val=c.val*Γ.L.val:=H; have hF : F.val=C.val*Γ.L.val:= (A.S.oneStep m p).exact_size
  have hi: Larger (G:=G) (A.clock.op m p):= by
    have hi := Nat.le_of_dvd C.pos (show c.val∣C.val from ⟨n,hn⟩)
    have hc : f.val≤ F.val:= le_trans (Eq.le hV) ((Nat.mul_le_mul_right Γ.L.val hi).trans_eq hF.symm)
    exact ⟨he.1, he.2.1.trans hc, he.2.2.trans_le hi⟩
  let T:Forest (decreed (P:=Γ) hV):= t; let B:= circuit (h:=hV) (H:=hF) hn ht T
  obtain ⟨ρ,hρ,hη,hq⟩:= Q.stationed hk he T (h:=hV)
  obtain ⟨r,hr,hb,hζ⟩:= Q.stationed hk hi B (h:=hF)
  let R := K.stationary N m p B
  have hC : ClassicalMatch (S:=stepped Z hF) B W.clip (A.params m).clip u v R := M.classicalPart N m p hm B
  have hR : r=ᶠ[𝓝 0] R := critical_single (S:=stepped Z hF) (Classical.arbitrary _) hr.critical (M.critical N m p hm B).1 hζ hb
  have hz : ClassicalMatch (S:=stepped Z hF) B W.clip (A.params m).clip u v r:= by
    intro i hi t; obtain ⟨hk,hp,hC⟩:=hC i hi t
    let g x:=tested (S:=stepped Z hF) B t W.clip u x (r x); let h x:=tested (S:=stepped Z hF) B t W.clip u x (R x)
    have ht:g=ᶠ[𝓝 0] h:= hR.mono fun x hx=> congr_arg (tested (S:=stepped Z hF) B t W.clip u x) hx
    exact ⟨hk.congr_of_eventuallyEq ht, hp, ((ht.iteratedFDeriv ℝ _).self_of_nhds).trans hC⟩
  have hK : FiniteBound (S:=stepped Z hF) B u v W.clip (A.params m).clip (K.alpha N m) O r (P.Γ j) (P.c j) (A.clock.loopCap (m+1)) := by
    obtain ⟨h,h₀,h₁,h₂⟩:= M.retains N m p hm B
    have he t : thermal (S:=stepped Z hF) B t W.clip u r O=ᶠ[𝓝 0] thermal (S:=stepped Z hF) B t W.clip u R O := hR.mono fun i hi=>by unfold thermal; rw [hi]
    refine ⟨Work.F05.hessian_pos hζ hb hr.critical, fun t=>(h₀ t).congr_of_eventuallyEq (he t), h₁,fun t i j s τ hs ht=>?_⟩
    change |iteratedFDeriv ℝ 2 _ _ _-_| ≤ _; rw [((he t).iteratedFDeriv ℝ 2).self_of_nhds]; exact h₂ t i j s τ hs ht
  exact ⟨ρ,hρ,expressed hn ht Q T hr hρ.critical _ _ hz, surge hn ht Q T hr hρ.critical hk he hi ho hK (P.posC j).le (P.pos _).le ((show (1:ℝ)≤2 from by norm_num).trans (Push.PriceCompiler.cap_ge ..))⟩
end YM.PhysicalNext.Repeat.Pane
