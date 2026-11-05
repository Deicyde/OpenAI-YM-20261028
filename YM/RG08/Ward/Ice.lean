import YM.RG08.Ward.Bays

/-! # Extract loop-Ward from all-grade and horizon-wise finite fits. No interchange
w/fixed slices or coupling resets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset
open PertExtension.Series.Tested PertExtension.Series.Radial
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f n : Side} {G : Gauge}
variable {V W : ℝ→ Link G n} {Q : Pot G 2} {p : Air G}

-- StepData-independent tests on paths.
def EquivalentNear (U V : ℝ→ Link G n) :=
    (∃ s : Signed, ∀ᶠ t in 𝓝 0,input G n (V t)=pull s 0 (input G n (U t))) ∨
    (∃ (k : ℝ→Site n→G.El) (z : G.El), Tendsto k (𝓝 0) (𝓝 (fun _=>z)) ∧ ∀ᶠ t in 𝓝 0,input G n (V t)=gauge (k t) (input G n (U t)))
lemma EquivalentNear.comp' (h : EquivalentNear V W) (t : ℝ→ℝ) (ht : Tendsto t (𝓝 0) (𝓝 0)) : EquivalentNear (V∘t) (W∘t) := by
  rcases h with ⟨s,hs⟩ | ⟨k,z,hk,he⟩
  · exact Or.inl ⟨s,ht.eventually hs⟩
  exact Or.inr ⟨k∘t,z,hk.comp ht,ht.eventually he⟩
lemma EquivalentNear.switch (h : EquivalentNear V W) {V' W'} (he : V'=ᶠ[𝓝 0]V) (hp : W'=ᶠ[𝓝 0] W): EquivalentNear V' W' := by
  rcases h with ⟨s,hs⟩| ⟨k,z,hk,hh⟩
  · refine Or.inl ⟨s, ?_⟩; filter_upwards [hs,he,hp] with i hx hu hr; rw [hr,hu,hx]
  refine Or.inr ⟨k,z,hk,?_⟩; filter_upwards [hh,he,hp] with i hx hu hr; rw [hr,hu,hx]
-- `Candidate.stepVote` to contracted cutoffs and sectors
abbrev suitify (U : ℝ→Link G n) (t : ℝ) := t•U t
def Beacon (n : Side)(p : Air G)(Q : Pot G 2) : Prop := ∀ i (v w : ℝ→Link G n), AnalyticAt ℝ v 0 → AnalyticAt ℝ w 0 →
    EquivalentNear (suitify v) (suitify w) → Fit (i+1) (fun t=> oblige Q p i t (v t)) (fun t=> oblige Q p i t (w t))

variable (Q p)
-- keep rank0 subtraction always, available in F'
def excise (F : Air G) (e r) := if r=0 then 0 else F e r
lemma excise_below {p : Air G} (h : Decked p) : Decked (excise p) := fun i j=> by unfold excise; split_ifs; simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff]; next => exact h i j
@[simp] lemma excise_heap (p : Air G) : Halt (excise p) := by simp [Halt,excise]
lemma excise_note (u : Link G n)(k : ℕ) (t : ℝ) : oblige Q p k t u= oblige Q (excise p) k t u+ ∑ i∈range (k+1), t^i* stanza (p i 0) n 0 := by
  unfold oblige; rw [add_assoc,← sum_add_distrib]; congr 1; apply sum_congr rfl; intro i _; unfold grand; rw [← mul_add, sum_range_succ' _ (i+2),Finset.sum_range_succ' _ (i+2)];
  have hh : stanza (p i 0) n u = stanza (p i 0) n 0 := congr_arg (recital (p i 0) n) (Subsingleton.elim ..)
  simp [excise, hh]
lemma excise_beacons (h : Beacon n p Q) : Beacon n (excise p) Q := by
  intro i v w hv hw he; have H:=h i _ _ hv hw he
  simp_rw [excise_note Q p] at H -- loop!? includes excise recursion! restrict pattern
  obtain ⟨C,hC,hS⟩:=H; refine ⟨C,hC,hS.mono fun x hx=> ?_⟩; simpa only [Pi.sub_apply,add_sub_add_right_eq_sub] using hx

-- take exactly N = k+2 - 2q with N≥2
variable {Q p}
private def tuned (x : ℝ) (v : ℝ→Link G n) (t : ℝ):= x • v (t*x)
lemma tuned_word (x : ℝ) (h : AnalyticAt ℝ V 0) : AnalyticAt ℝ (tuned x V) 0 :=
    (analyticAt_const (v:=x)).smul (AnalyticAt.comp (f:=fun t=>t*x) ((zero_mul x).symm ▸ h) (analyticAt_id.mul analyticAt_const))
lemma tuned_suit (x : ℝ) (v : ℝ→Link G n) : suitify (tuned x v)=(fun t=> suitify v (t*x)) := funext fun t=> smul_smul t x _
lemma tuned_fit (k : ℕ)(h : Beacon n p Q) (hp : AnalyticAt ℝ V 0) (he : AnalyticAt ℝ W 0) (hV : EquivalentNear (suitify V) (suitify W)) (x : ℝ) :
    Fit (k+2+1) (fun t=>t^2 * oblige Q p k t (tuned x V t)) (fun t=>t^2 * oblige Q p k t (tuned x W t)) := by
  have hx : EquivalentNear (suitify (tuned x V)) (suitify (tuned x W)) := by simp_rw [tuned_suit]; exact hV.comp' _ (by simpa only [id_eq,zero_mul] using! ((continuous_id (X:=ℝ)).mul_const x).tendsto 0)
  have H:= (h k _ _ (tuned_word x hp) (tuned_word x he) hx).right (ruler 2 2 le_rfl); rw [show 2+(k+1)= k+2+1 by omega] at H; exact H

lemma arc_extraction {I : Finset ℕ}{F H : ℕ→ℝ→ℝ} {k : ℕ} (h : ∀ i,ContDiffAt ℝ ∞ (F i) 0)(hp : ∀ i,ContDiffAt ℝ ∞ (H i) 0)
    (he : ∀ x:ℝ,Fit (k+1) (fun t=> ∑ i∈I,t^(2*i)*F i (t*x)) (fun t=>∑ i∈I, t^(2*i)*H i (t*x))) (q : ℕ)(hq:q ∈ I)(j : ℕ) (hj : j+2*q ≤ k) : ink (F q) j=ink (H q) j := by
  let u:=j+2*q; let Y (F : ℕ→ℝ→ℝ) (x t : ℝ):= ∑ i∈I,t^(2*i)*F i (t*x)
  let m (F : ℕ→ℝ→ℝ) := fun i x=>(if 2*i≤u then x^(u-2*i)*ink (F i) (u-2*i) else 0)
  have hx (F : ℕ→ℝ→ℝ) (hf : ∀ i, ContDiffAt ℝ ∞ (F i) 0) (x : ℝ) : ContDiffAt ℝ ∞ (Y F x) 0 ∧ ink (Y F x) u= ∑ i∈I, m F i x := by
    have hv i : ContDiffAt ℝ ∞ (fun t=> F i (t*x)) 0 := ((zero_mul x).symm ▸ hf i).comp (f:=fun t=>t*x) 0 (contDiffAt_id.mul contDiffAt_const)
    let z i := fun t:ℝ=>t^(2*i)* F i (t*x)
    have he i : ContDiffAt ℝ ∞ (z i) 0 := (contDiffAt_id.pow _).mul (hv i)
    exact ⟨ContDiffAt.sum (f:=z) (fun i _=>he i), (ink_list I z (fun i _=> he i) u).trans (sum_congr rfl fun i _=> by unfold z m; rw [ink_t_pow (f:=fun t=> F i (t*x)) (hv i),pulse_c (hf i)])⟩
  have hl : (fun x=>∑ i∈I,m F i x)=(fun x=>∑ i∈I,m H i x) := by
    funext x; rw [← (hx _ h x).2, ← (hx _ hp x).2]; exact aspiredV (he x) (ink_aspire (hx _ h x).1) (ink_aspire (hx _ hp x).1) hj
  have hr (p : ℕ→ℝ→ℝ) : ink (fun x=> ∑ i∈I,m p i x) j= ink (p q) j := by
    have hu : u-2*q=j:=by unfold u; omega
    rw [ink_list I (m p) (fun i _=> by unfold m; split_ifs; exact (contDiffAt_id.pow _).mul contDiffAt_const; exact contDiffAt_const),sum_eq_single_of_mem q hq]
    · unfold m; simp only [show 2*q ≤ u by unfold u; omega, if_true,hu,ink_single]
    intro i hi he; unfold m; split; next hy=> rw [ink_single,if_neg]; omega -- split may differ
    next H=> exact congr_fun ink_z _
  rw [← hr F,← hr H,hl]

lemma parts_beacon (h : Beacon n p Q) (hd : Decked p) (he : Halt p) (hp : AnalyticAt ℝ V 0) (hy : AnalyticAt ℝ W 0) (hx : EquivalentNear (suitify V) (suitify W))
    (k q : ℕ) : Fit (k+2+1) (grand (k+2) (sector Q p q) n ∘ suitify V) (grand (k+2) (sector Q p q) n ∘ suitify W) := by
  let S := k+2*q
  let Y (v : ℝ→Link G n) := fun i t=> ∑ j∈trimmed S i, stanza (sector Q p i j) n (suitify v t)
  have hO (v : ℝ→Link G n) (hv:AnalyticAt ℝ v 0) (i) : ContDiffAt ℝ ∞ (Y v i) 0 := ContDiffAt.sum fun j _=> (stanza_smooth ..).contDiffAt.of_le le_top|>.comp _ ((contDiffAt_id.smul hv.contDiffAt).of_le le_top)
  have hg (v : ℝ→Link G n) (x t:ℝ) : t^2* oblige Q p S t (tuned x v t)= ∑ i∈range (S+2+1),t^(2*i)* Y v i (t*x) := by
    rw [← loopCount Q _ hd he]; apply sum_congr rfl; intro i hi; unfold Y; rw [show suitify v (t*x)=t • tuned x v t from Eq.symm (congr_fun (tuned_suit x v) t)]
  have hf (U : ℝ→Link G n) : Y U q=grand (k+2) (sector Q p q) n ∘ suitify U := by funext t; unfold grand Y; rw [show trimmed S q=_ from (show trimmed S q=range (k+2+1) by ext i; unfold trimmed S; simp only [mem_range,mem_filter]; omega), Function.comp_apply,Finset.sum_apply]
  rw [← hf V,← hf W]; refine pulse_bound (fun i hi=> ?_) (hO V hp q) (hO W hy q)
  exact arc_extraction (hO V hp) (hO W hy) (fun x=>by have he' := tuned_fit S h hp hy hx x; simp_rw [hg] at he'; exact he') q (show q∈range (S+2+1) by simp only [mem_range]; unfold S; omega) i (by unfold S; have hy:=mem_range.mp hi; omega)
end YM.RG08.Reflect
