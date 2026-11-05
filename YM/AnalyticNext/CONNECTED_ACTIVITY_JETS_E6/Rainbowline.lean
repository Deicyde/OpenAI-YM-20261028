import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arcus
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Street
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tint

/-!
# Exponential budgets for motions of our plate *including derivatives*

All-post-L. Need appropriate inverse estimates to spend on cap receipt.
Works even at flags (witness actual stencil duties) where no activity
promises field Differentiable but the color-log expression needs an
invariant proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush
variable {v z r Q : ℝ} {k : ℕ} {U : E → Config G c} {x : E}

namespace Gate

def kernelGrowth (B : ℕ) (G : Gauge) (v : ℝ) := let k:=4*B*(v*royalty G); k+(v+v)+k
def cable (P : Teller G) (Gd : Patch) (K : ℝ) := scale*((2*K*Real.exp (P.top.width*(predReach Gd+7:ℝ)))*
    (royalty G*((royalty G *(1*royalty G))*royalty G)))

-- Charge displacement reversal on leg if pulls orientations s
theorem whirl (X : Coat T F) (D : Patch) (hd : S.patch=D) (h : Room P S T X.x) (hf : Mode U x k v)
    (p : Coat.Target c f G) (q : Tubular f G) (C : ℝ) (hC : 0<C) (hp : SliceRows.Bounded T P.top.width C) :
    Brush k (cable P D C / wt P.top.width (aim S p) (along S q)) (kernelGrowth X.B G v)
      (fun u => (vary X (U u)).form p q) x := by
  let K:=4*(X.B:ℝ)*(v*royalty G)
  have hv : 0≤v := hf.pos; have hz := royalty_ge G
  have hb : 0≤ kernelGrowth X.B G v := by unfold kernelGrowth; positivity
  let A := P.top.width; let E' := cable P D C
  have he' : 0 ≤ cable P D C/wt P.top.width (aim S p) (along S q) := by
    apply div_nonneg _ (wt_pos ..).le; have hp:=scale_pos; unfold cable; positivity
  by_cases ht : X.Hot q.1
  swap
  · obtain ⟨_,_,hw,-⟩:=h.accepted.feeds; simp_rw [(show ∀ i:E,_ from fun i=> (vary X (U i)).cold q ht hw p)]
    exact (Brush.certified hb 0).climb (by rwa [norm_zero]) le_rfl
  by_cases hl : separation (aim S p) (along S q) ≤ X.B/4
  swap
  · have he i : (vary X (U i)).form p q=0 := (vary X (U i)).plume h p q (lt_of_not_ge hl)
    simp_rw [he]; exact (Brush.certified hb 0).climb (by rwa [norm_zero]) le_rfl
  let s:=p.1.1; let w:=p.1.2; let i:Bond f := (StepData.sendBonds p.1.1 0).symm q.1
  have hs : Channel.edge s i=q.1 := (StepData.sendBonds p.1.1 0).apply_symm_apply _
  let o:=focus S w
  have hx : separation o (atEdge S i) ≤ X.B := by
    apply le_trans _ (show X.B/4+1 ≤ X.B from by have hu:100≤X.B := h.sight.1; omega)
    change separation (s.act o) (atEdge S q.1) ≤ _ at hl
    rw [← separation_signed (s:=s)]; apply (separation_triangle _ (atEdge S q.1) _).trans; rw [← hs]
    apply add_le_add (hs.symm ▸ hl)
    -- compare projected edge case explicitly
    cases hy : s.flip i.2
    · rw [positive s i hy]; dsimp only [atEdge]; rw [S.ratio.parent_signed S.patch.odd_side,separation_self]; decide
    rw [negative s i hy]; dsimp only [atEdge]; rw [S.ratio.parent_signed S.patch.odd_side,separation_signed,separation_comm]
    exact parent_step ..
  have hQ : ∀ u:E,(vary X (U u)).lens (sing q)=sing q := by
    intro u; change X.lens _=_; funext b; by_cases H : b=q.1
    · subst b; simp [Coat.lens,ht]
    simp [Coat.lens,sing,H]
  let R (u : E) := spinRow S (carrier o (pull s 0 (U u))) (displacement s (sing q) (replica S.ratio (U u)))
  let e u:= R u i
  have hR u : R u=Pi.single i (e u) := by
    ext1 j; by_cases he : j=i
    · subst j; rw [Pi.single_eq_same]
    rw [Pi.single_eq_of_ne he]; apply norm_eq_zero.mp
    unfold R spinRow; rw [G.norm_adjoint, size_displacement]
    simp only [sing, Pi.single_eq_of_ne (show Channel.edge s j≠q.1 from by rw [← hs]; exact sendEdge_injective s 0|>.ne he), norm_zero]
  have heq: Brush k (royalty G) K (fun y=> G.mat (carrier o (pull s 0 (U y)) (atEdge S i))) x := by
    apply (tour (carriage o (atEdge S i)) o hv (turn hf s).atLink).climb le_rfl
    unfold K; gcongr; exact_mod_cast (mileage ..).trans (Nat.mul_le_mul_left 4 hx)
  let M:=royalty G *(1*royalty G)
  have hm : Brush k M (v+v) (fun t=> displacement s (sing q) (replica S.ratio (U t)) i) x := by
    unfold displacement; rw [hs]; simp only [sing,Pi.single_eq_same]; split_ifs; next ht =>
      let f' t:= (replica S.ratio (U t) q.fst)⁻¹
      have hr : Brush k (royalty G) v (G.mat ∘ f') x := Blaze.reverse (f:=fun t=> replica S.ratio (U t) q.1) (recopy S hf.atLink q.1)
      have hx : Brush k 1 0 (fun _:E=> ConnectedActivityE6.dot G q.2) x := (Brush.certified (le_refl 0) _).climb (by simp [ConnectedActivityE6.dot]) le_rfl
      simpa only [add_zero] using! (Blaze.decorate hr hx).opposite
    exact (Brush.certified (by linarith : 0≤v+v) (ConnectedActivityE6.dot G q.2)).climb (by simp only [ConnectedActivityE6.dot, OrthonormalBasis.norm_eq_one]; unfold M; nlinarith only [hz]) le_rfl
  let G' := 2*C*Real.exp (P.top.width*(predReach D+7:ℝ))
  let N:= royalty G*(M*royalty G)
  have htZ : Brush k N (kernelGrowth X.B G v) e x := Blaze.decorate (g:=fun t=> carrier o (pull s 0 (U t)) (atEdge S i)) heq hm
  obtain ⟨_,_,hB,-⟩:= h.accepted.feeds
  let Z : G.Color→ₗ[ℝ] G.Color :=
    { toFun c:= barField T X.R (Pi.single i c) w
      map_add' c d := by rw [Pi.single_add, bar_add T hB]
      map_smul' c d := by rw [Pi.single_smul,bar_smul T hB]; rfl }
  let V:= Z.toContinuousLinearMap; let g:= wt P.top.width (aim S p) (along S q)
  have hg : ‖V‖≤ G'/g := by
    have hh : 0 < g := wt_pos ..
    have hp b:= input_decays h.accepted hC hp w i b X.R
    apply ContinuousLinearMap.opNorm_le_bound _ (show 0≤G'/g by unfold G'; positivity)
    intro c; let Q : ℝ:= Real.exp (P.top.width * distAt S i o)
    have he : g ≤ Real.exp P.top.width * Q := by
      have hi : (distAt S q.1 (s.act o):ℝ) ≤ ↑(distAt S i o)+1 := by exact_mod_cast hs ▸ projects S s o i
      unfold Q g wt; rw [← Real.exp_add]; apply Real.exp_monotone
      change P.top.width*(distAt S q.1 (s.act o):ℝ)≤ _; nlinarith only [mul_le_mul_of_nonneg_left hi P.top.width_pos.le]
    rw [div_mul_eq_mul_div,le_div_iff₀ hh,mul_comm ‖V c‖]
    apply (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
    rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (hp c) (Real.exp_pos _).le).trans_eq
    unfold G'; rw [hd]; rw [show P.top.width*(predReach D+7:ℝ)=P.top.width+P.top.width*(predReach D+6:ℝ) by ring, Real.exp_add]; ring
  by_cases hs : X.selected p.1.1 (spot S p.1.2)
  · have hu (u) : (vary X (U u)).form p q=scale*stand (fun _ : Unit=> V (e u)) ((),p.2) := by
      unfold Coat.form Coat.motion stand; simp only [of_apply,if_pos (show (vary X (U u)).selected .. from hs),hQ]; unfold orientedRow straightened; change scale*barField T X.R (R u) w p.2=_; rw [show R u= _ from hR u]; rfl
    simp_rw [hu]; refine ((colorEvaluated p.2 (htZ.report V hg)).smul scale).climb ?_ le_rfl
    rw [Real.norm_of_nonneg scale_pos.le]; unfold cable G' g N M; apply le_of_eq; ring
  have he u : (vary X (U u)).form p q=0 := by unfold Coat.form of; change scale*_ = _; unfold stand Coat.motion; rw [if_neg (show ¬(vary X (U u)).selected .. from hs)]; exact mul_zero _
  simp_rw [he]; exact (Brush.certified hb _).climb (by rwa [norm_zero]) le_rfl
end Gate
end YM.ConnectedActivityE6.Blaze
