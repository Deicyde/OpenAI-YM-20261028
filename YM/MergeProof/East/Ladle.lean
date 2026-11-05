import YM.MergeProof.East.Oast

/-!
# Choose lift after labels calibration by actual covariance matrices
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Lattice Wilson Price  Cells MeasureTheory
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d k N p i:ℕ}
local notation "K"=>Nat
variable {C:Family G}(h:C.Makes)(hr:C.ref d≤ k)(hk:k ≤ N) (b:ℝ)
local notation "F"=> C.labels.level d
variable (T:Module.End ℂ (C.label d)) (H:Tested C d k N p T)
-- not true outside tails. zero
variable (C) in
def ladd (b:ℝ)(k N p d:ℕ)(T:Module.End ℂ (C.label d)) : C.label d→ₗ[ℂ] C.label d :=
    if h:Bijective T then (LinearEquiv.ofBijective T h).symm.toLinearMap ∘ₗ (C.labels.level d).scaled (Price.shrink C k N p)⁻¹ ∘ₗ weightTag C d b else 0
local notation "Z"=> ladd C b k N p d T
lemma facsimile (b c:ℝ)(P : Family G) (d:ℕ): weightTag P d (b*c)=weightTag P d b ∘ₗ weightTag P d c := by ext i j; simp [weightTag];ring
lemma horse (T) (x:C.label d)(t r:ℝ): ladd C (t*r) k N p d T x=ladd C t k N p d T (weightTag C d r x):=by
    unfold ladd; split; swap; · rfl
    rw [facsimile];rfl
-- offset‐only variants later
include h hr hk H
lemma poured (x:C.label d): Solves C b d k N p T x (Z x):= by
    let F':= F; have ht:= H.bijective C h hr hk T; simp only [Solves,ladd,dif_pos ht]; rw [LinearMap.comp_apply,LinearEquiv.coe_coe]
    rw [show T ((LinearEquiv.ofBijective T ht).symm _)= _ from (LinearEquiv.ofBijective T ht).apply_symm_apply _]; exact F'.scaled_inv (shrink_pos C h hk p).ne' _
lemma pure_start : Z (F).e0=C.refUnit d:= by
    obtain ⟨u,hu,hv⟩:=solve C h hr hk H ((C.labels.level d).e0) b; apply (hv _ (poured h hr hk b T H _)).trans (hv _ ?_).symm
    unfold Solves; rw [H.unit,Frame.scaled_unit,weight_tag_zero]
lemma purer (x:C.label d): Z (star x)=star (Z x):= by
    obtain ⟨u,hu,hv⟩:=solve C h hr hk H (star x) b; apply (hv _ (poured h hr hk b T H _)).trans (hv _ ?_).symm
    unfold Solves; rw [H.preserves,show ∀ v:C.label d,(F).scaled (shrink C k N p) (star v)=star ((F).scaled (shrink C k N p) v) from fun x=> funext fun i=>by simp, poured h hr hk b T H, weight_tag_real]
lemma rider (hu:∀ s x,T (mir F s x)=mir F s (T x))(s:Signed)(x : C.label d): Z (mir F s x)=mir F s (Z x):=by
    obtain ⟨u,hU,hv⟩:=solve C h hr hk H (mir F s x) b; apply (hv _ (poured h hr hk b T H _)).trans (hv _ ?_).symm
    unfold Solves; rw [hu]; unfold mir; rw [Frame.scaling,poured h hr hk b T H]; exact Extra.Histories.Motion.act_diag F (fun j=> (b:ℂ)^j.1) s.ortho _
-- operator norm.Pay positions.Or adapt
omit H hk in
lemma sun (x:C.label d): ∃ A : ℝ,∀ N p T,k ≤ N→Tested C d k N p T→ ‖ladd C b k N p d T x‖≤A:= by
    let L:= F; let v:= weightTag C d b x; let r:= 2*C.path.levels.clock.monitor k;let R:= L.coeffSize (L.scaled r v)
    refine ⟨outward C d k * C.S.a k^d*(2*R),fun N p T hk hT=>?_⟩
    let Y:= ladd C b k N p d T x; let a:= shrink C k N p; have ht : 0<a:= shrink_pos C h hk p;have hz:a⁻¹≤r:= shrink_min C h hk p
    have hQ : L.scaled a (T Y)=v:= poured h hr hk b T hT x
    have hB: T Y=L.scaled a⁻¹ v:= by have he:=L.scaled_inv (inv_ne_zero ht.ne') (T Y); rw [inv_inv,hQ] at he; exact he.symm
    have he : L.coeffSize (T Y) ≤ R:= by
       rw [hB]; unfold R Frame.coeffSize; have h' : 0<r:= (inv_pos.mpr ht).trans_le hz
       apply Finset.sum_le_sum; intro j _; rw [Frame.scaled_apply,Frame.scaled_apply,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity),Complex.norm_real,Real.norm_of_nonneg (by positivity)]; gcongr
    refine (show ‖Y‖ ≤ L.coeffSize Y from (pi_norm_le_iff_of_nonneg (Work.G08.size_nonneg L _)).2 (fun i=> Finset.single_le_sum (fun _ _=> norm_nonneg _) (Finset.mem_univ i))).trans ((reference_size C h hr hk p Y).trans ?_)
    exact mul_le_mul_of_nonneg_left ((hT.cost C T Y).trans (mul_le_mul_of_nonneg_left he zero_le_two)) (mul_nonneg (zero_le_one.trans (outward_nn ..)) (pow_nonneg (C.S.a_pos _).le _))
end YM.Next.Rank.East
