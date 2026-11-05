import YM.FullVolume.Tess.Zoom
/- placement infrastructure. Macro differences.N≥j. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Filter Function Set Metric MeasureTheory Lattice RG Ray Asymptotics
open PhysicalNext.Repeat.Muse
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp
variable (S:Schedule){n N j m p:ℕ}
def ascending (p:ℕ)(hp:j≤ N) (x:Positions n): Positions n:= (S.toDepth hp p).count.val • x
lemma arriving (p:ℕ)(x:Positions n): ascending (N:=N) S p le_rfl x=x:=by simp [ascending,Schedule.toDepth,Schedule.steps]
lemma wraps (p:ℕ)(hp:j≤ N) (x:Positions n): wrap _ ∘ ascending S p hp x=(S.toDepth hp p).embed ∘ ((wrap _ : Cover →+ Site (S.side j p)) ∘ x):= funext fun i=> ((S.toDepth hp p).embed_wrap _).symm
lemma arrivesP (p:ℕ)(hp:j≤ N)(x:Positions n): tag (S.a N) (ascending S p hp x)=tag (S.a j) x:=by
    let g:= S.toDepth hp p
    refine PiLp.ext fun i=>PiLp.ext fun a=>?_ ; change S.a N* ((g.count.val • (x i)) a:ℝ)=S.a j*(x i a:ℝ)
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,← mul_assoc]; rw [Schedule.embeds_scale S g]
abbrev terrace (p:ℕ)(hp:j≤ N)(l:List (MotionIndex n))(F:Positions n→ℂ): Positions n→ℂ:= deltas (S.a j) (l.map drive) (F ∘ (ascending S p hp))
lemma ascends (p:ℕ)(hp:j ≤ N)(F:Positions n→ℂ)(l:List (MotionIndex n))(x:Positions n) : terrace S p hp l F x= blurs (S.toDepth hp p).count.val (l.map drive) (deltas (S.a N) (l.map drive) F) (ascending S p hp x):=by
    let g:= S.toDepth hp p; let n_:=g.count.val; let t:=S.a N
    have hh(x y:Positions _): ascending (n:=«n») S p hp (x+y)=ascending S p hp x+ (S.toDepth hp p).count.val • y:=smul_add ..
    induction l generalizing x with
    | nil=> rfl
    | cons i l ih=>
       let w:=drive i; let L:= l.map drive; let z:= ascending S p hp x; let H:= blurs n_ L (deltas t L F)
       have he: terrace S p hp l F (x+w)= H (z+n_ • w):=by rw [ih,hh]
       change (S.a j:ℂ)⁻¹*(terrace S p hp l F (x+w)-terrace S p hp l F x) = blur w n_ (blurs n_ L (delta w t (deltas t L F))) z
       rw [thru,same_delta,he,ih]; congr 2; rw [← S.embeds_scale g,mul_comm,Complex.ofReal_mul,Complex.ofReal_natCast]
private lemma driveBlurs (t L c v:ℝ) (ht:0<t)(x:Points n)(A:ℕ)(l:List (MotionIndex n))(ha:0<A)(hv:t*A ≤ v)(F:Positions n→ℂ)(y:Positions n)
   (hx:∀ z:Positions n,dist (tag t z) x≤ L → ‖F z‖≤c)(he:dist (tag t y) x≤ L - l.length*v): ‖blurs A (l.map drive) F y‖ ≤ c:=by
   induction l generalizing y with
   | nil=> exact hx y (by simpa using he)
   | cons i l ih=>
      change ‖blur _ _ (blurs _ _ F) _‖ ≤ _; apply blurred ha; intro j hj
      apply ih; apply (dist_triangle _ (tag t y) x).trans _; rw [paidDist y t ht i]; simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at he
      nlinarith only [hv,he,mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hj.le) ht.le]
lemma fareWarp {p:ℕ}(hp:j ≤ N)(F:Positions n→ℂ)(l:List (MotionIndex n))(x:Positions n)(c:ℝ)
   (ht: ∀ y:Positions n, dist (tag (S.a N) y) (tag (S.a j) x) ≤ l.length*S.a j→
       dist (deltas (S.a N) (l.map drive) F y) (deltas (S.a N) (l.map drive) F (ascending S p hp x)) ≤ c): dist (terrace S p hp l F x) (deltas (S.a N) (l.map drive) F (ascending S p hp x))≤ c:=by
    let z:= ascending S p hp x; let g:= S.toDepth hp p; let G:= deltas (S.a N) (l.map drive) F
    have he:= driveBlurs (S.a N) _ c (S.a j) (S.a_pos _) (tag (S.a j) x) g.count.val l g.count.property (S.embeds_scale g).le (G-fun _=>G z) z (fun u h=> show ‖G u-G z‖ ≤ c from (dist_eq_norm (G u) (G z)).symm.trans_le (ht u h)) (by unfold z; rw [arrivesP,dist_self,sub_self])
    rw [map_sub,blur_fixed g.count.val g.count.property] at he; rw [ascends]; exact (dist_eq_norm ..).trans_le he
end YM.FullVolume
#print axioms YM.FullVolume.ascends
