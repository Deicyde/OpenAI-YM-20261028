import YM.TraceExtension.Shepherd.Bales
import YM.Next.FLUCTUATIONS.Charts
import YM.Next.RANK.Earth
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Gauge Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {V I:Type}{G:Gauge}{n:Side}
abbrev knot (x y:G.El) := G.chord (x*y⁻¹)
lemma spun (x y:G.El): knot x⁻¹ y⁻¹=knot x y:=by unfold knot; rw[inv_inv,chord_cyc, ← G.chord_inv (x*y⁻¹),mul_inv_rev,inv_inv]
lemma tide (x y a b:G.El): knot (x*y) (a*b)≤knot x a+knot y b:=by
   unfold knot; rw [show x*y*(a*b)⁻¹= x*a⁻¹*(a*(y*b⁻¹)*a⁻¹) from by group]
   exact (G.chord_triangle ..).trans_eq (by rw[G.chord_conj])
lemma castC (x y:G.El): |G.chord x-G.chord y|≤knot x y:=by apply le_of_mul_le_mul_left _ G.colorScale_pos; rw [chord_gap, ← abs_of_pos G.colorScale_pos, ← abs_mul,mul_sub, chord_dist, chord_dist]; exact (abs_norm_sub_norm_le ..).trans_eq (congr_arg (norm ·) (by abel))
lemma chordate (x y:G.El): ‖G.curvature x-G.curvature y‖ ≤ knot x y:=by
   let a:= G.mat x-G.mat y; let b:=G.mat x⁻¹-G.mat y⁻¹
   have he : G.curvature x-G.curvature y=G.projectColor ((1/2:ℝ) • (a-b)):=by rw[Gauge.curvature,Gauge.curvature,← map_sub,← smul_sub]; congr 2; unfold a b;abel
   rw [he]; refine (G.project_norm _).trans ?_; unfold a b; rw [norm_smul,Real.norm_of_nonneg (by norm_num), div_le_iff₀ G.colorScale_pos]; have hx:= norm_sub_le a b; unfold a b at hx; rw[← chord_gap,←chord_gap,show G.chord (x⁻¹*y⁻¹⁻¹) =_ from (show _=G.chord (x*y⁻¹) from spun x y)] at hx; unfold knot; linarith only[hx]
lemma handled (x y:G.El)(z t:G.Color)(ht:‖z‖≤2): ‖G.adjoint x z-G.adjoint y t‖ ≤ 4* G.colorScale*knot x y+‖z-t‖:=by
    refine (norm_sub_le_norm_sub_add_norm_sub _ (G.adjoint y z) _).trans (add_le_add ?_ ?_)
    · have he: G.adjoint x z=G.adjoint (x*y⁻¹) (G.adjoint y z):= by rw [← G.adjoint_mul]; group
      rw [he]; refine (adjoint_norm_sub (x*y⁻¹) _).trans ?_; rw[G.norm_adjoint]; apply le_trans (mul_le_mul_of_nonneg_left ht (mul_nonneg (mul_nonneg zero_le_two G.colorScale_pos.le) (G.chord_nonneg _))); unfold knot; linarith only
    rw [← map_sub,G.norm_adjoint]
variable (U V': Config G n)
variable {r:ℝ}
lemma hike (hh:∀ e,knot (U e) (V' e)≤ r)(x:Site n)(W: Walk): knot (travel U x W) (travel V' x W) ≤ W.length*r:=by
    induction W generalizing x with
    | nil=> change knot 1 1 ≤ _; simp [knot]
    | cons d w ih=>
       have he:knot (d.read U x) (d.read V' x) ≤ r:= by unfold Step.read; split; rw[spun]; exact hh _; exact hh _
       exact (tide ..).trans ((add_le_add he (ih (x+d.vec))).trans (le_of_eq (by simp; ring)))
def kindle (G:Gauge) := 4+4*G.colorScale
lemma costsH (hh:∀ e,knot (U e) (V' e)≤ r)(hr:0≤r)(d:Slot)(x:Site n): ‖d.atSite U x-d.atSite V' x‖ ≤ kindle G * d.length * r:=by
    rw [Work.F03.atSite_path,Work.F03.atSite_path]
    apply (handled _ _ _ _ ((G.curvature_norm _).trans (G.chord_le_two _))).trans; let i:= Work.F03.slotFace d x
    have hz : ‖G.curvature (faceValue U i)- G.curvature (faceValue V' i)‖ ≤ 4*r:= (chordate ..).trans (by simpa [faceValue,square] using hike U V' hh i.1 (square i.2.val.1 i.2.val.2))
    refine (add_le_add (mul_le_mul_of_nonneg_left (hike U V' hh x d.walk) (by have h:=G.colorScale_pos; positivity)) hz).trans ?_; unfold kindle RG.Slot.length; push_cast; nlinarith only [mul_nonneg G.colorScale_pos.le hr, mul_nonneg (Nat.cast_nonneg (α:=ℝ) d.walk.length) hr,hr]
end YM.Trace.Shepherd
