import YM.AnalyticNext.QUARTIC_MATCH.Exchange


/-!
# Counting and paying assignments on actual path jets

No divided powers in these estimates. Use finite labelled slots; billing sums
include contacts and lower actions too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Matrix Analysis
open scoped Topology ContDiff BigOperators

variable {ι α : Type*} {X Y Z E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]

def hook (S : Finset ι) (d : ι→X) := fun k : Fin S.card => d (S.equivFin.symm k).val

def bill (S : Finset ι) (d : ι→X) (f : X→Y) (x : X) := iteratedFDeriv ℝ S.card f x (hook S d)

lemma lists (S : Finset ι) (d : ι→X) (f : X→Y) (x : X) (h : ContDiffAt ℝ ω f x)
    (m : ℕ) (u : Fin m ≃ ↥S) : bill S d f x=iteratedFDeriv ℝ m f x (fun i => d (u i).1) := by
  obtain rfl : m=S.card := by simpa using Fintype.card_congr u
  unfold bill
  rw [← sym_Jet (h.of_le (show (S.card : WithTop ℕ∞)≤ω from le_top)) _ (u.trans S.equivFin)]
  congr; ext i; simp [hook]

lemma univEstimate {n : ℕ} (d : Fin n→X) (f : X→Y) (x : X) (h : ContDiffAt ℝ ω f x) :
    bill Finset.univ d f x=iteratedFDeriv ℝ n f x d := by
  let e : Fin n ≃ ↥(Finset.univ : Finset (Fin n)) := ⟨fun i => ⟨i,Finset.mem_univ _⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  exact lists Finset.univ d f x h n e

lemma blank (d : ι→X) (f : X→Y) (x : X) : bill ∅ d f x=f x := iteratedFDeriv_zero_apply _
lemma germ {S : Finset ι} {d : ι→X} {f g : X→Y} {x : X} (h : f =ᶠ[𝓝 x] g) : bill S d f x=bill S d g x := by
  unfold bill; rw [(h.iteratedFDeriv ℝ S.card).eq_of_nhds]
lemma smooth_rate {S : Finset ι} {d : ι→X} {f : X→Y} {x : X} (h : ContDiffAt ℝ ω f x) : ContDiffAt ℝ ω (bill S d f) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ => X) Y (hook S d)).contDiff.contDiffAt.comp _ (h.iteratedFDeriv_right (by simp))
lemma sum_bill (D : Finset α) (S : Finset ι) (d : ι→X) (f : α→X→Y) (x : X) (h : ∀ i∈D, ContDiffAt ℝ ω (f i) x) :
    bill S d (fun x => ∑ i∈D, f i x) x=∑ i∈D, bill S d (f i) x := by
  unfold bill; rw [show (fun x => ∑ i∈D, f i x)=∑ i∈D,f i from funext fun x => (Finset.sum_apply ..).symm,
    iteratedFDeriv_sum_apply ..]; simp only [_root_.sum_apply];
  exact fun i hi => (h i hi).of_le le_top
lemma plus_rate (S : Finset ι) (d : ι→X) {f g : X→Y} {x : X} (h : ContDiffAt ℝ ω f x) (u : ContDiffAt ℝ ω g x) :
    bill S d (fun v => f v+g v) x=bill S d f x+bill S d g x := by unfold bill; rw [show (fun v => f v+g v)=f+g from rfl,iteratedFDeriv_add_apply (h.of_le le_top) (u.of_le le_top)]; rfl
lemma minor_rate (S : Finset ι) (d : ι→X) {f g : X→Y} {x : X} (h : ContDiffAt ℝ ω f x) (u : ContDiffAt ℝ ω g x) :
    bill S d (fun v => f v-g v) x=bill S d f x-bill S d g x := by unfold bill; rw [show (fun v => f v-g v)=f-g from rfl,iteratedFDeriv_sub_apply (h.of_le le_top) (u.of_le le_top)]; rfl
lemma smul_price (S : Finset ι) (d : ι→X) {f : X→Y} {x : X} (h : ContDiffAt ℝ ω f x) (v : ℝ) :
    bill S d (v • f) x=v • bill S d f x := by unfold bill; rw [iteratedFDeriv_const_smul_apply (h.of_le le_top)]; rfl
lemma empty_price (S : Finset ι) (d : ι→X) (x : X) : bill S d (fun _ : X => (0:Y)) x=0 := by simp [bill]
lemma left_price (S : Finset ι) (d : ι→X) (L : Y →L[ℝ] Z) {f : X→Y} {x : X} (h : ContDiffAt ℝ ω f x) :
    bill S d (L ∘ f) x=L (bill S d f x) := by unfold bill; rw [L.iteratedFDeriv_comp_left h le_top]; rfl
lemma readdress (S : Finset ι) (d : ι→X) (L : X →L[ℝ] Y) (x : X) {f : Y→Z} (h : ContDiff ℝ ω f) :
    bill S d (f ∘ L) x=bill S (L ∘ d) f (L x) := by unfold bill; rw [ContinuousLinearMap.iteratedFDeriv_comp_right]; rfl; exact h; exact le_top
lemma bill_bound (S : Finset ι) (d : ι→X) (f : X→Y) (x : X) : ‖bill S d f x‖ ≤ ‖iteratedFDeriv ℝ S.card f x‖*∏ i∈S,‖d i‖ := by
  apply ((iteratedFDeriv ℝ S.card f x).le_opNorm _).trans_eq (congr_arg _ ?_)
  exact (S.equivFin.symm.prod_comp (fun i => ‖d i.val‖)).trans (Finset.prod_attach S (fun i => ‖d i‖))

section multi
variable [DecidableEq ι]
lemma counted {S : Finset ι} {i : ι} (hi : i∉S) (d : ι→X) (f : X→Y) (x : X) (h : ContDiffAt ℝ ω f x) :
    bill (insert i S) d f x=D (d i) (bill S d f) x := by
  let u := (finSuccEquiv S.card).trans <| (Equiv.optionCongr S.equivFin.symm).trans <| (Finset.subtypeInsertEquivOption hi).symm
  rw [lists (insert i S) d f x h (S.card+1) u]
  rw [show (fun i => d (u i).val)=Fin.cons (d i) (hook S d) by
    funext j; refine Fin.cases ?_ ?_ j
    · simp [u, Finset.subtypeInsertEquivOption]; rfl
    intro k; simp [u,hook,Finset.subtypeInsertEquivOption]; rfl]
  exact cons_jet (h.of_le le_top) _ _
lemma alone (d : ι→X) (f : X→Y) (x : X) (h : ContDiffAt ℝ ω f x) (i : ι) : bill {i} d f x=D (d i) f x := by
  rw [show ({i}:Finset ι)=insert i ∅ by simp,counted (by simp) d f x h, show bill ∅ d f=f from funext (blank d f)]
omit [DecidableEq ι] in
lemma mute {S : Finset ι} (h : S.Nonempty) (d : ι→X) (x : X) (y : Y) : bill S d (fun _ : X => y) x=0 := by
  unfold bill; rw [iteratedFDeriv_const_of_ne (𝕜:=ℝ) (Finset.card_ne_zero.mpr h)]; rfl

/-- Include derivative *labels*, not commuting the multiplication. -/
lemma account (φ : Y→L[ℝ] Z→L[ℝ] E) (S : Finset ι) (d : ι→X) (f : X→Y) (g : X→Z) (x : X)
    (h : ContDiffAt ℝ ω f x) (e : ContDiffAt ℝ ω g x) :
    bill S d (fun u => φ (f u) (g u)) x = ∑ T∈S.powerset, φ (bill T d f x) (bill (S\T) d g x) := by
  let p := fun u => φ (f u) (g u)
  induction S using Finset.induction_on generalizing x with
  | empty => simp [blank]
  | @insert i S hi ih =>
    let F (t : Finset ι) (x) := φ (bill t d f x) (bill (S\t) d g x)
    have hf (t) : DifferentiableAt ℝ (F t) x :=
      (((φ.contDiff.contDiffAt.comp x (smooth_rate h)).clm_apply (smooth_rate e)).differentiableAt (by simp))
    have hu (t : Finset ι) (ht : t∈S.powerset) :
        D (d i) (F t) x = φ (bill t d f x) (bill ((insert i S)\t) d g x)+φ (bill (insert i t) d f x) (bill ((insert i S)\(insert i t)) d g x) := by
      have ht' := Finset.mem_powerset.mp ht
      have he : i∉t := Finset.notMem_mono ht' hi
      have hx : i ∉ S\t := by simp [hi]
      rw [show insert i S \ t = insert i (S\t) by ext j; by_cases h : j=i <;> simp [h,he],
        show insert i S \ insert i t=S\t by ext j; by_cases h : j=i <;> simp [h,hi],counted hx _ _ _ e,counted he _ _ _ h]
      unfold F; rw [D_apply]
      congr 2
      rw [D_comp φ.differentiableAt,φ.fderiv]
      exact (smooth_rate h).differentiableAt (by simp)
      · exact φ.differentiableAt.comp _ ((smooth_rate h).differentiableAt (by simp))
      exact (smooth_rate e).differentiableAt (by simp)
    rw [counted hi d p x ((φ.contDiff.contDiffAt.comp _ h).clm_apply e)]
    trans D (d i) (fun y => ∑ t∈S.powerset, F t y) x
    · exact GermD _ ((h.eventually (by simp)).mp (((e.eventually (by simp)).mono fun y ey fy => ih y fy ey)))
    rw [D,(HasFDerivAt.fun_sum (fun t (_ : t ∈ S.powerset) => (hf t).hasFDerivAt)).fderiv, _root_.sum_apply, Finset.sum_powerset_insert hi,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => hu i hi
end multi
end YM.AnalyticNext.QuarticMatch.Estimate
