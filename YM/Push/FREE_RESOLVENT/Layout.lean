import YM.Next.FLUCTUATIONS.Locality
import YM.Push.FREE_RESOLVENT.PathsAffine
import YM.Push.FREE_RESOLVENT.Torus


/-!
# Footprint arithmetic for weighting jets

`named`: output location of a row in its channel. The positive-bond
registration map *also* charges an endpoint for a flipped bond. Distinct
placements of a possible test are still counted as distinct θ labels. No
contamination from continuations of charts on different masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.E03
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c n : Side} {S : StepData c f} {r k : ℕ} {σ V A : ℝ}

def home (S : StepData c f) (i : Slot G f r) := S.ratio.parent i.1

def named (S : StepData c f) (s : Signed) (i : Slot G f r) := S.ratio.parent (affine s 0 i.1)
def hearth (i : Slot G c r) := i.1
def namedCo (s : Signed) (i : Slot G c r) := affine s 0 i.1

def ray (G : Gauge) (c : Side) (i : raw G c) : Vec G c 1 := Pi.single i 1

lemma home_volume (S : StepData c f) (r : ℕ) (t : ℝ) (h : 0 < t) :
    (native c).Volume (home (G:=G) (r:=r) S) t (torusPay (Co S.patch.L (PAC G r)) t) := by
  let E := splitCo S.ratio (PAC G r)
  rw [show home (G:=G) (r:=r) S=Prod.fst ∘ E from funext fun i => by simp only [home,E,Function.comp_apply,split_co]]
  exact (volume c _ _ h).comp E.injective
lemma named_volume (S : StepData c f) (s : Signed) (r : ℕ) (t : ℝ) (h : 0 < t) :
    (native c).Volume (named (G:=G) (r:=r) S s) t (torusPay (Co S.patch.L (PAC G r)) t) := by
  let E := Equiv.prodCongr (StepData.sendSites (c:=f) s 0) (Equiv.refl (PAC G r))
  exact (home_volume S r t h).comp E.injective
lemma co_volume (G : Gauge) (c : Side) (s : Signed) (r : ℕ) (t : ℝ) (h : 0 < t) :
    (native c).Volume (namedCo (G:=G) (r:=r) s) t (torusPay (PAC G r) t) := by
  let E := Equiv.prodCongr (StepData.sendSites (c:=c) s 0) (Equiv.refl (PAC G r))
  exact (volume c _ _ h).comp E.injective
lemma ray_nn (i : raw G c) : ‖ray G c i‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => by
  by_cases h : j=i <;> simp [ray,h]

lemma move_separates (S : StepData c f) (s : Signed) (g q : Site f) :
    separation (S.ratio.parent (affine s 0 g)) (S.ratio.parent (affine s 0 q)) =
    separation (S.ratio.parent g) (S.ratio.parent q) := by
  simp only [affine,add_zero,S.ratio.parent_signed S.patch.odd_side,separation_signed]

-- coordinate projection on a *fixed* set for proving locality of jets
section stencil
variable {α : Type*} [Fintype α] [DecidableEq α] {X : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

def chop (t : α → Prop) [DecidablePred t] : (α → ℝ) →L[ℝ] α → ℝ := LinearMap.toContinuousLinearMap ({
  toFun x i := if t i then x i else 0
  map_add' x y := by ext; split <;> simp_all
  map_smul' r x := by ext; split <;> simp_all } : (α → ℝ) →ₗ[ℝ] α → ℝ)

lemma peel (l : List α) {i} (hi : i ∈ l) {t : α → Prop} [DecidablePred t] {F : (α → ℝ) → X}
    (he : F =ᶠ[𝓝 0] F ∘ chop t) (hc : ContDiffAt ℝ l.length F 0)
    (hv : jet (fun i : α => Pi.single i 1) F l 0 ≠ 0) : t i := by
  by_contra h
  apply hv
  rw [identical _ he l, jet, Next.Foundations.jets_linear (chop t) hc,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hi
  apply ContinuousMultilinearMap.map_coord_zero (i:=j)
  change chop t (Pi.single (l.get j) 1)=0
  rw [hj]
  ext a
  change (if t a then _ else 0)=(0:ℝ); by_cases H : a=i <;> simp_all
end stencil

def coarse (G : Gauge) (x : Site c) (R : ℕ) := chop fun i : raw G c => separation x (hearth i) ≤ R

/-- Applies to original unregularized backdrop at the place queried. -/
lemma back_uses (S : StepData c f) (B : Vec G c 1) (x : Site c) (R : ℕ) (e : Edge (Site f))
    (hx : separation x (S.ratio.parent e.1) ≤ R) :
    backdrop S ((coarse G x R) B) e = backdrop S B e := by
  unfold backdrop replica; split
  · rfl
  rw [Work.F03.represent_link, Work.F03.represent_link]
  congr 1; ext l
  change (if separation x (S.ratio.parent e.1) ≤ R then _ else 0)=_
  rw [if_pos hx]; rfl

/-- Compute locality using `travel_pull` and its *same* whole orientation,
so even paths winding are compared by charging their labels, not their
minimum torus representative length. -/
lemma edge_local (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q : ℕ) :
    let w := (W.row (plaqEquiv.symm i.2.1) q).2.walk
    edgework S s W r i j q=edgework S s W r i j q ∘ (coarse G (named S s i) w.length) := by
  intro w; ext B
  have ht : travel (shone S s B) i.1 w = travel (shone S s ((coarse G (named S s i) w.length) B)) i.1 w := by
    unfold shone; rw [travel_pull, travel_pull]
    refine Next.Fluctuations.travel_near S.ratio.parent (parent_step S) _ _ _ _ w.length (by simp) ?_
    exact fun e he => (back_uses S B _ _ e he).symm
  simp only [Function.comp_apply, edgework, element]; rw [ht]

lemma edge_slot (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q : ℕ) :
    let R := (W.row (plaqEquiv.symm i.2.1) q).2
    edgework S s W r i j q ≠ 0 → j.1=wrap f R.offset+i.1 := by
  intro R; contrapose!
  intro h; funext; simp only [edgework,element]; split
  · rw [if_neg]; · simp
    intro he; exact h (congr_arg Prod.fst he)
  rfl

lemma zero_null {τ : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (x : E) (v : τ → E) (l : List τ) : jet v (0:E→F) l x=0 := by
  by_cases h : l=[]; · rw [h,zeroth]; rfl
  exact jet_const v l h 0 x

lemma forward (S : StepData c f) (s : Signed) (W : PathData G) (r : Admit) (i j : tile G f)
    (q : ℕ) {l : List (raw G c)} (he : jet (ray G c) (edgework S s W r i j q) l 0 ≠ 0) :
    let p := (W.row (plaqEquiv.symm i.2.1) q).2
    separation (named S s i) (named S s j) ≤ p.length ∧ ∀ x ∈ l, separation (named S s i) (hearth x) ≤ p.length := by
  intro p
  have hh : p.walk.length ≤ p.length := Nat.le_add_right ..
  constructor
  · have hi : edgework S s W r i j q ≠ 0 := fun hv => he (by rw [hv, zero_null])
    have hv := edge_slot S s W r i j q hi
    apply le_trans _ hh
    unfold named; rw [move_separates, show j.1=stop i.1 p.walk from ?_]; exact Work.E03.sep_walk _ (parent_step S) ..
    have hr : stop i.1 p.walk=wrap f p.offset+i.1 := by
      unfold RG.Slot.offset
      rw [wrap_stop_cover,map_zero,add_comm,← Work.E03.stop_add_left]; simp
    exact hv.trans hr.symm
  intro x hx
  exact (peel l hx (t:=fun x => separation (named S s i) (hearth x) ≤ p.walk.length)
    (EventuallyEq.of_eq (edge_local S s W r i j q)) (polar_edge S s W r i j q l.length (by norm_num : (0:ℝ)<1)) he).trans hh

-- Finite TestD.pay uses exponent with whole l; nonneg keep exact.
open Mark
lemma plumb {X τ : Type*} (D : Cost X) (p : X) (a : τ → X) (l : List τ) (hσ : 0 ≤ σ) (M : ℝ)
    (h : ∀ i∈l, D.d p (a i) ≤ M) :
    (positions D a σ).pay l p ≤ Real.exp (l.length*σ*M) := by
  induction l with
  | nil => simp [pay]
  | cons b l ih =>
    rw [pay]
    calc
      _ ≤ Real.exp (σ*M)*Real.exp (l.length*σ*M) := mul_le_mul
        (Real.exp_monotone (mul_le_mul_of_nonneg_left (h b (by simp)) hσ)) (ih fun i hi => h i (List.mem_cons_of_mem b hi))
        (pay_pos ..).le (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, List.length_cons]; push_cast; congr 1; ring

end YM.FreeResolvent.Affine
