import YM.UVExtension.Projection.Query.View

/-! Two concrete variations. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Filter Function Finset Set
open scoped Topology BigOperators ContDiff Classical
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] {f : ℕ→ X}
lemma through_coords (h : ∀ L : X →ₗ[ℝ] ℝ, Arrives fun i=> L (f i)): Arrives f:=by
  let b := (Module.finBasis ℝ X).equivFun
  obtain ⟨z,hz⟩:= Arrives.columns (f:= fun i=> b (f i)) (fun i=> h (((LinearMap.proj i)).comp b.toLinearMap))
  exact (Arrives.post (f:=fun i=> b (f i)) ⟨_,hz⟩ b.symm.toContinuousLinearEquiv.continuous).copy (Eventually.of_forall fun i=> b.symm_apply_apply (f i))

def limitView : MenuView ℕ where
    pace _ := Arrives
    base _ x := Arrives.steady x
    mono h _:=h
    add h hp:= h.plus hp
    mul h hp:= h.times hp
    post h hs hc hf:= by
      obtain ⟨z,hz⟩:= through_coords h
      exact ⟨_, hf _ (hc.mem_of_tendsto hz (Eventually.of_forall hs)) |>.tendsto |>.comp (tendsto_nhdsWithin_iff.mpr ⟨hz,Eventually.of_forall hs⟩)⟩
lemma travels {i} : limitView.sees i f ↔ Arrives f:= ⟨through_coords, fun h L=> h.post L.continuous_of_finiteDimensional⟩

open Polynomial
variable {I : Type} (u : I→ℝ)
def arc (u : I→ ℝ) (k : ℕ) (f : I→ℝ):= ∃ p : ℝ[X], p.natDegree ≤ k ∧ ∀ x,f x=p.eval (u x)
lemma arc_const {I} (u : I→ℝ) (p : ℝ) (v : ℕ) : arc u v fun _=> p:= ⟨C p,by simp,by simp⟩
lemma arc_zero {p : I→ℝ} (h : arc u 0 p) (i j): p i=p j:=by
  obtain ⟨q,hq,he⟩:=h
  rw [he,he,Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hq)]; simp

def straight : MenuView I where
    pace := arc u
    base i p:= arc_const u p i
    mono h hp:= by obtain ⟨p,hr,h⟩:=h; exact ⟨p,le_trans hr hp,h⟩
    add h he:= by obtain ⟨q,hq,h⟩:=h; obtain ⟨p,hp,he⟩:=he; exact ⟨q+p,(natDegree_add_le ..).trans (max_le hq hp),fun i=> by simp [h,he]⟩
    mul h he:= by obtain ⟨q,hq,h⟩:=h; obtain ⟨p,hp,he⟩:=he; exact ⟨q*p,(natDegree_mul_le ..).trans (add_le_add hq hp),fun i=> by simp [h,he]⟩
    post {Y} _ _ _ {f} {p} _ h _ _ _:= by
      cases isEmpty_or_nonempty I with
      | inl e=> exact ⟨0,by simp,fun i=> isEmptyElim i⟩
      | inr e=> obtain ⟨z⟩:=e
                have he i: f i=f z:= by
                  let b := (Module.finBasis ℝ Y).equivFun; apply b.injective; ext1 j; exact arc_zero u (h ((LinearMap.proj j).comp b.toLinearMap)) i z
                exact ⟨C (p (f z)),by simp,fun i=> by change p (f i)=_; rw [he,eval_C]⟩
lemma straight_axis : (straight u).pace 1 u:= ⟨Polynomial.X,by simp,fun i=>by simp⟩
end YM.UVExtension.Projection
