import YM.Push.FREE_RESOLVENT.PeriodAffine


/-!
# Transport a *single* gauge-tag cost through an inverse

Different actual embeddings of the free space invalidate subtracting the
kernels entrywise. Use the **identity-completed** version. Interpolate the
completed forward precisions (root unchanged, tag discrete, *not* interpolating
any physical gauge variable!) to transfer one tag mark using the
already-paid jet engine. The extra derivatives on this polynomial auxiliary
parameter thereby pay the location v without paying volume. Projection masks
are not differentiated on either trajectory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent
open Lattice RG Precision Tree Matrix Mark TestD Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {α β ι κ τ X E G : Type*}
namespace Lever

section smooth
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable (v : τ → E)
/-- B is the first parameter. None denotes location reserved for change
of actual tag mask. -/
def guides (t : Option τ) : E × ℝ := t.elim (0,1) fun i => (v i,0)

def castLift (A : E → G) (y : E × ℝ) := A y.1

def stir (A : E → G) (y : E × ℝ) := y.2 • A y.1

def multiple (l : List (Option τ)) : Prop := l.length > (l.filterMap id).length + 1

-- partial jets restrict to charts (even if map evaluated at s ≠0)
lemma restriction (l : List τ) (r : ℝ) {A : E × ℝ → G} (h : ContDiffAt ℝ l.length A (0,r)) :
    jet (guides v) A (l.map some) (0,r) = jet v (fun x => A (x,r)) l 0 := by
  let L := ContinuousLinearMap.inl ℝ E ℝ
  let a : E × ℝ := (0,r)
  let F (y : E × ℝ) := A (y+a)
  have ht : ContDiffAt ℝ l.length F 0 := by
    have he : ContDiffAt ℝ l.length A (0+a) := by rw [zero_add]; exact h
    exact he.comp (f:=fun z => z+a) 0 (contDiffAt_id.add contDiffAt_const)
  calc
    _ = jet (guides v ∘ some) A l a := Affine.mark_map ..
    _ = jet (L ∘ v) F l 0 := by unfold jet F; rw [iteratedFDeriv_comp_add_right,zero_add]; rfl
    _ = jet v (fun x => F (L x)) l 0 := Affine.all_dir l L v ht
    _ = _ := by congr 1; funext x; unfold F L a; simp [- Prod.mk.injEq]



lemma filter_lengths (l : List (Option τ)) : (l.filterMap id).length ≤ l.length := List.length_filterMap_le ..
lemma noTag {l : List (Option τ)} (h : none ∉ l) :
    (l.filterMap id).map some=l := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp_all

lemma loses {l : List (Option τ)} : none ∈ l → (l.filterMap id).length < l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases a with
    | none => intro h; exact Nat.lt_succ_of_le (filter_lengths l)
    | some a => intro h; exact Nat.add_lt_add_right (ih (by simpa using h)) _
-- castLift restriction in derivative.
open scoped Classical in
lemma casts (l : List (Option τ)) {A : E → G} {x : E} (t : ℝ) (h : ContDiffAt ℝ l.length A x) :
    jet (guides v) (castLift A) l (x,t) = if none ∉ l then jet v A (l.filterMap id) x else 0 := by
  -- use composition with pi.fst and h; rewrite at nonzero via translation.
  let L := ContinuousLinearMap.fst ℝ E ℝ
  let P := fun z : E => A (x+z)
  let Q := fun z => P (L z)
  have he : ContDiffAt ℝ l.length P 0 := by
    refine ContDiffAt.comp (g:=A) _ ?_ (contDiffAt_const.add contDiffAt_id)
    simpa using h
  have ht : ∀ z, Q z=castLift A ((x,t)+z) := fun z => rfl
  have hw : jet (guides v) (castLift A) l (x,t)=jet (guides v) Q l 0 := by
    unfold jet; rw [funext ht, iteratedFDeriv_comp_add_left]; simp
  rw [hw, ← Affine.all_dir l L (guides v) he]; split
  next h0 =>
    let w := l.filterMap id
    have he : l=w.map some := (noTag h0).symm
    rw [show jet (L ∘ guides v) P l 0 = jet v P w 0 from ?_]
    · unfold jet P; rw [iteratedFDeriv_comp_add_left, add_zero]
    rw [he, Affine.mark_map]; rfl
  next h0 =>
    obtain ⟨b,hb⟩ := List.mem_iff_get.mp (show none ∈ l from Classical.not_not.mp h0)
    exact ContinuousMultilinearMap.map_coord_zero _ b (by simp only [Function.comp_apply,hb]; rfl)

open scoped Classical in
lemma blend (l : List (Option τ)) {A : E → G} {x : E} {t : ℝ} (h : ContDiffAt ℝ l.length A x) :
    jet (guides v) (stir A) l (x,t) = if none ∉ l then t • jet v A (l.filterMap id) x else
      if multiple l then 0 else jet v A (l.filterMap id) x := by
  induction l generalizing x t with
  | nil => rw [zeroth]; simp [zeroth,stir]
  | cons q l ih =>
    have hf : ContDiffAt ℝ (↑(l.length+1):ℕ∞ω) (stir A) (x,t) := contDiffAt_snd.smul (h.comp (f:=Prod.fst) (x,t) contDiffAt_fst)
    rw [jet_step (guides v) q _ hf]
    let w := l.filterMap id
    have hx : ∀ᶠ z : E × ℝ in 𝓝 (x,t), jet (guides v) (stir A) l z = if none ∉ l then z.2 • jet v A w z.1 else
      if multiple l then 0 else jet v A w z.1 := by
        filter_upwards [(continuous_fst.tendsto (x,t)).eventually (h.eventually (by simp))] with z hz
        exact ih (x:=z.1) (t:=z.2) (smooth_of_le hz (by simp))
    have hh : ContDiffAt ℝ (↑(w.length+1):ℕ∞ω) A x := smooth_of_le h (Nat.add_le_add_right (filter_lengths _) 1)
    have hk : DifferentiableAt ℝ (jet v A w) x := jet_diff v w hh
    have hg : HasFDerivAt (fun z : E × ℝ => jet v A w z.1) ((fderiv ℝ (jet v A w) x) ∘L ContinuousLinearMap.fst ℝ E ℝ) (x,t) :=
      hk.hasFDerivAt.comp (f:=Prod.fst) (x,t) hasFDerivAt_fst
    by_cases hL : none ∉ l
    · have hb : w.length=l.length := by exact (by simpa only [List.length_map,w] using congr_arg List.length (noTag hL))
      simp only [if_pos hL] at hx
      have hp := ((hasFDerivAt_snd (𝕜:=ℝ) (p:=(x,t))).smul hg).congr_of_eventuallyEq hx
      cases q with
      | none =>
        simp only [List.mem_cons_self, not_true, ↓reduceIte]
        rw [hp.fderiv,if_neg (show ¬multiple (none::l) from ?_)];
        · simp [guides,w]
        change ¬ w.length+1 < l.length+1; omega
      | some q =>
        have hv : (some q::l).filterMap id=q::w := rfl
        rw [if_pos (by simp_all), hv, jet_step v _ _ hh, hp.fderiv]; simp [guides]
    have hM : none ∈ l := Classical.not_not.mp hL
    simp only [if_neg hL] at hx
    rw [if_neg (show ¬ none ∉ q::l from by simp_all)]
    by_cases hH : multiple l
    · simp only [if_pos hH] at hx
      have h : jet (guides v) (stir A) l =ᶠ[𝓝 (x,t)] fun _ => 0 := hx
      have hk : w.length+1 < l.length := hH
      rw [if_pos]
      · rw [h.fderiv_eq]; simp
      cases q
      · change w.length+1 < l.length+1; omega
      change w.length+1+1 < l.length+1; omega
    simp only [if_neg hH] at hx
    have hp : HasFDerivAt (jet (guides v) (stir A) l) _ (x,t) := hg.congr_of_eventuallyEq hx
    have hl : l.length = w.length+1 := by
      unfold multiple at hH; have ht : (l.filterMap id).length < l.length := by
        exact loses hM
      unfold w; omega
    rw [hp.fderiv]
    cases q with
    | none =>
      rw [if_pos]; · simp [guides]
      change w.length+1 < l.length+1; omega
    | some q =>
      have hv : (some q::l).filterMap id=q::w := rfl
      rw [if_neg (show ¬multiple _ from ?_), hv, jet_step v _ _ hh]
      · rfl
      unfold multiple; rw [hv]; simp [hl]
end smooth
end Lever
end YM.FreeResolvent
