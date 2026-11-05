import YM.WilsonBulk.Staves.Sentinel
import YM.WilsonBulk.Staves.Stockings

/-!
# Descent/generator passes: MUST carry winding/roll costs already (Whisper).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Lattice Laurent Function Filter Bloch Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset Equiv
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {α : Type} {G : Gauge} {u e q k j n : ℕ} {c : Side} {D : ℕ→Side} {I : Library G}

lemma shift_card (p : Cover) (i : PotentialForm) (t : Bool) : wrap c (backed t i p) = backed t i (wrap c p) := by cases t <;> simp [backed]
lemma plume_like (t : Bool) (a : PotentialForm) (u i : G.ColorIndex) (v : Legs G.ColorIndex q)
    (w : Legs (Mark G) (k+q+1)) (T : Text (Cloth G) (k+1)) (p : Public T) (hd : Tendsto (fun i=>(D i).val) atTop atTop) :
    Tendsto (fun j=> plume backed t a u i v (coupon (D j) _ T) (small (D j) (Cloth G) ∘ w)) atTop (𝓝 (plume backed t a u i v T w)) := by
  refine legs_succ (fun w : Legs (Mark G) (k+q+1)=> Tendsto (fun j=> plume backed t a u i v (coupon (D j) _ T) (small (D j) _ ∘ w)) atTop (𝓝 (plume backed t a u i v T w))) (fun x w=> ?_) w
  refine legs_plus (k:=k) (fun w=> Tendsto (fun j=> plume backed t a u i v (coupon (D j) _ T) (small (D j) _ ∘ (hitch x w))) atTop (𝓝 (plume backed t a u i v T (hitch x w)))) (fun y z=> ?_) w
  simp only [hitch_comp,append_comp,plume,castTail,hitch_zero,crop_hitch]
  by_cases h:x.2=(coord 0,i); swap; · have hg n: (small (D n) _ x).2≠(coord 0,i):=h; simp only [if_neg h, if_neg (hg _)]; exact tendsto_const_nhds
  have hg n: (small (D n) _ x).2=(coord 0,i):=h; simp_rw [if_pos h, if_pos (hg _), tassel_pay]
  let p':=cameo backed t a x.1
  have hv (j:ℕ) : (fun k:G.ColorIndex=> selvedge (cameo backed t a (small (D j) (Cloth G) x).1) k)=small (D j) (Cloth G) ∘ selvedge p' := funext fun k=> Prod.ext (shift_card x.1 a t).symm rfl
  let E := selvedge p' ∘ v
  by_cases hk:z=E
  · subst z
    -- simplify via hv directly here too
    simp_rw [show ∀ j,(selvedge (cameo backed t a (small (D j) (Cloth G) x).1):G.ColorIndex→_)=_ from hv]; simp only [E,← Function.comp_assoc,p', ↓reduceIte,margin]; have ht:= Public.introduction T p hd (hitch (selvedge p' u) y) (by omega); simp only [hitch_comp,p'] at ht; refine ht.congr' (Eventually.of_forall fun i=>?_); dsimp only; rw [show selvedge (cameo backed t a (small (D i) _ x).1) u= _ from congr_fun (hv i) u]; rfl
  rw [if_neg hk]; apply Tendsto.congr' _ (tendsto_const_nhds (x:=0)); obtain ⟨i,hi⟩:= Function.ne_iff.mp hk; filter_upwards [small_eq_event hd (z i) (E i)] with j hj
  rw [if_neg]; intro H; apply hi; apply hj; exact (congr_fun H i).trans (congr_fun (hv j) (v i))

lemma spiro_descent (w : Legs (Mark G) (k+q+1)) (T : Text (Cloth G) (k+1)) (p : Public T) (hd : Tendsto (fun i=>(D i).val) atTop atTop) :
    Tendsto (fun j=> spiro backed (coupon (D j) _ T) q (small (D j) (Cloth G) ∘ w)) atTop (𝓝 (spiro backed T q w)) := by
  simp only [spiro,tailBuff,castTail,Function.comp_apply,crop_comp,polish, Pi.smul_apply, Finset.sum_apply,smul_eq_mul,escort,margin,ribbons]
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun j _=> tendsto_finsetSum _ fun a _=> tendsto_finsetSum _ fun b _=> tendsto_finsetSum _ fun c _=> tendsto_finsetSum _ fun d _=> ?_); simp_rw [Function.comp_assoc, ← hitch_comp]; exact (plume_like j a c b d _ T p hd).const_mul _

lemma sentries (h : Whisper I) (e n : ℕ) : (∑ q∈ range (e+1), proceeding backed I e n q)=0 := by
  let D:=cascade (1:Side); have hp q (v : Legs (Mark G) (n+1)) : Tendsto (fun i=> proceeding backed (Sheet.issue (D i) I) e n q (small (D i) (Cloth G) ∘ v)) atTop (𝓝 (proceeding backed I e n q v)) := by
    by_cases hq:q≤e ∧ q≤n
    · simp only [proceeding,dif_pos hq,Pi.smul_apply]; unfold postage castTail; simp_rw [Function.comp_apply,crop_comp,escort, margin,Function.comp_assoc, ← hitch_comp, smul_eq_mul]
      exact (spiro_descent _ _ (h.palm _ _) (cascade_up (c:=(1:Side)))).const_mul _
    simp only [proceeding,dif_neg hq]; exact tendsto_const_nhds
  ext1 i; rw [Finset.sum_apply]; apply tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum _ fun k _=> hp k i) tendsto_const_nhds (Eventually.of_forall fun j=>?_); dsimp only; rw [← Finset.sum_apply]; exact congr_fun (sentry (Sheet.issue (D j) I) (h.guns _) (h.palm.at_issue _ h.style) e n) _

def strategy (d : Bool →PotentialForm→α→α) (I : Record (α × Cloth G)) (e n) := ∑ i∈range e, proceeding d I e n (i+1)
lemma submission (h : Whisper I) (e n : ℕ) : diss backed (I e (n+1)) = - ((n+1:ℕ):ℝ)⁻¹ • (strategy backed I e n) := by
  have hp := sentries h e n; rw [sum_range_succ',proceeding_free backed I h.style.coherent,← neg_eq_iff_add_eq_zero] at hp
  -- check signs Lean unary - precedence
  calc _ = ((n+1:ℕ):ℝ)⁻¹ • (((n+1:ℕ):ℝ) • diss backed (I e (n+1))) := (inv_smul_smul₀ (by positivity) _).symm
       _ = _ := by rw [← hp, neg_smul,smul_neg]; rfl
end Parapet
end YM.WilsonBulk
