import YM.TraceExtension.Xo.Miser
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Xo
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}
lemma lush_v(v:Gal G n)(hv:v∈rains G n):ContDiffAt ℝ ω (lush v ∘ input G n) 0:=by
    have h:= memo_t (Y:=v) (hv.1) (input G n) (Army.powL (v:=id) contDiffAt_id) (input_zero ..)
    exact ContDiffAt.sum (fun _ _=> h _ _)
lemma forever (G:Gauge): ∃ A B:ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (n:Side)(Y Y': Axis→Gal G n), (∀ i,Y i∈ rains G n∧Y' i∈rains G n)→ ∀ (a C:ℝ), 0<a→0 ≤ C→ (∀ i,Estate 0 (bottom (Y i-Y' i)) a (fun _=>C))→∀ b:G.ColorIndex,
    let c:=a/5/4/5; |(Holt b (fun i=>lush (Y i) ∘ input G n)).re-(Holt b (fun i=>stubJ (lush (Y' i)) ∘ input G n)).re| ≤ B*(ramt 3 (Fin 2) c+ramt 2 (Fin 2) c)*(A*C*countCost c):=by
    obtain ⟨A,hA,H⟩:=cooler G; obtain ⟨B,hB,h⟩:=WiltsPay; refine ⟨A,B,hA,hB,fun n Y V hp a C ha hC ht b=>?_⟩
    intro c; let X(i:Axis):=lush (Y i) ∘ input G n; let F(i:Axis):=lush (V i) ∘ input G n; let R(i:Axis):=stubJ (lush (V i)) ∘ input G n
    have hc:0<c:=by unfold c; positivity
    have he(i j:Axis): molt (0:Site n) ![mood G i b,mood G i b] (F j)=molt 0 ![mood G i b,mood G i b] (R j):=by
        let W:=F j; let f:= R j; have hh:f=W-fun _=> W 0:=by ext1 x; simp [f,W,R,F,stubJ]
        have hV: iteratedFDeriv ℝ 2 f 0=iteratedFDeriv ℝ 2 W 0:=by
            rw [hh,iteratedFDeriv_sub_apply]; rotate_left
            · exact (lush_v (V j) (hp j).2).of_le le_top
            · exact contDiffAt_const
            simp only [iteratedFDeriv_const_of_ne (show 2≠ (0:ℕ) by decide),Pi.zero_apply,sub_zero]
        have hv: ∀ i:Fin 2→Lines G n 1,entry (R j) 0 i=entry (F j) 0 i:=by intro i; unfold entry; rw[show iteratedFDeriv ℝ 2 (R j) 0=_ from hV]
        unfold molt; simp_rw[hv]
    rw [show Holt b R= Holt b F from ?_, ← Complex.sub_re, ← suite_minus b (fun i=>lush_v (Y i) (hp i).1) (fun i=> lush_v _ (hp i).2)]
    ·
      exact (Complex.abs_re_le_norm _).trans (h _ _ b _ c _ hc (mul_nonneg (mul_nonneg hA hC) (count_pos hc).le) (fun i=> H n (Y i) (V i) (hp i).1 (hp i).2 0 a C ha hC (ht i)))
    unfold Holt crest floft pia; simp_rw [← he]
end YM.Trace.Xo
