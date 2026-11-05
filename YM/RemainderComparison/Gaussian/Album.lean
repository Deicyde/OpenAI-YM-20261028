import YM.RemainderComparison.Gaussian.Treasury

/-!
 # Joint expenses before uncut integral. Keep price of each operand, no
 independent Gaussian products. Estimating the vacuum exponent on the
 actual chart requires its valuation or an explicit size condition (one
 may take temporary marker fugacities instead on multilogs; here work for
 exact coefficient products as factors, not exponentiated away).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n j m k i : ℕ} {v u D C A B : ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι
variable {U W : ℝ × E → Poll.Body ι → F} {V : ℝ × E → Poll.Body ι → ℝ}

lemma Picture.gather (h : Picture U D v u j C) (he : Picture W D v u j A) :
    Picture (fun x z => U x z+W x z) D v u j (C+A):= by
  refine ⟨add_nonneg h.expense he.expense, fun x hx=> ?_, fun x hx z hz=> ?_⟩
  · change StronglyMeasurable (_root_.Set.indicator _ (U x + W x)); rw [Set.indicator_add' ..]; exact (h.cut _ hx).add (he.cut _ hx)
  exact (h.budget x hx z hz).gathering (he.budget x hx z hz)
lemma Cloud.gather (h : Cloud U D v u j n C) (he : Cloud W D v u j n A) :
    Cloud (fun x z => U x z+W x z) D v u j n (C+A) := by
  refine ⟨h.toPicture.gather he.toPicture, fun y hy z=> ?_, fun R hR=> ?_⟩
  · exact ((h.view y hy z).gathering (he.view y hy z)).climb (by rw [add_mul]) le_rfl
  obtain ⟨d,hd,Q,hQ⟩:=h.satellite R hR; obtain ⟨d',hd',Q',hQ'⟩:=he.satellite R hR
  exact ⟨min d d',lt_min hd hd', _ ,(hQ.mend le_rfl (min_le_left ..) le_rfl le_rfl).gather (hQ'.mend le_rfl (min_le_right ..) le_rfl le_rfl)⟩
lemma Picture.still (q : F) (D v u : ℝ) (n : ℕ) :
    Picture (fun (_: ℰ) (_ : Ξ) => q) D v u n ‖q‖ :=
  ⟨norm_nonneg _,fun _ _=> stronglyMeasurable_const.indicator measurableSet_closedBall, fun _ _ _ _=> Brush.certified zero_le_one _⟩
lemma Cloud.still (q : F) (D v u : ℝ) (n : ℕ) :
    Cloud (fun (_: ℰ) (_ : Ξ) => q) D v u n 0 ‖q‖ :=
  ⟨Picture.still .., fun _ _ z=> by rw [vat,pow_zero,mul_one]; exact Brush.certified zero_le_one _, fun R _=> ⟨1,zero_lt_one,‖q‖, Picture.still ..⟩⟩
lemma Picture.axis_s (t : ℝ) (h : Picture U D v u j C) :
    Picture (fun x z=> t • U x z) D v u j (‖t‖*C) := by
  refine ⟨mul_nonneg (norm_nonneg _) h.expense, fun x hx=> ?_, fun x hx z hz=> (h.budget _ hx z hz).smul _⟩
  let s:=closedBall (0:Ξ) D
  rw [show s.indicator (fun z=>t • U x z)=(fun z=> t • s.indicator (U x) z) from funext fun z=> by by_cases H:z∈s <;> simp [Set.indicator,H]]
  exact StronglyMeasurable.smul (stronglyMeasurable_const (b:=t)) (h.cut x hx)
lemma Cloud.axis_s (t : ℝ) (h : Cloud U D v u j n C) :
    Cloud (fun x z=> t • U x z) D v u j n (‖t‖*C):= by
  refine ⟨ Picture.axis_s _ h.toPicture, fun x hx z=> ?_, fun R hR=> ?_⟩
  · rw [mul_assoc]; exact (h.view x hx z).smul _
  obtain ⟨d,hd,Q,hQ⟩:= h.satellite R hR; exact ⟨d,hd,_,hQ.axis_s _⟩
lemma cloud_sum {β : Type} (s : Finset β) (f : β→ ℰ→ Ξ→F) (a : β→ℝ)
    (hp : ∀ i∈s, Cloud (f i) D v u j n (a i)) :
    Cloud (fun x z=> ∑ i∈s, f i x z) D v u j n (∑ i∈s,a i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact (Cloud.still ..).raise le_rfl le_rfl le_rfl (by rw [norm_zero]) (Nat.zero_le _)
  | insert i s hi ih =>
    simp_rw [sum_insert hi]; apply (hp i (Finset.mem_insert_self ..)).gather (ih fun i hi=> hp i (Finset.mem_insert_of_mem hi))

lemma Picture.mix (h : Picture V D v u j C) (he : Picture U D v u j A) :
    Picture (fun x z=> V x z • U x z) D v u j (C*A*3^j) := by
  have hC:=h.expense; have hA:= he.expense
  refine ⟨by positivity,fun x hx=> ?_,fun x hx z hz=> Trace.paint (h.budget _ hx z hz) (he.budget _ hx z hz)⟩
  let s:=closedBall (0:Ξ) D
  rw [show s.indicator (fun z=>V x z • U x z)=(fun z=> s.indicator (V x) z • s.indicator (U x) z) from funext fun z=> by by_cases H:z∈s <;> simp [Set.indicator,H]]
  exact StronglyMeasurable.smul (h.cut x hx) (he.cut x hx)
lemma Cloud.mix (h : Cloud V D v u j n C) (he : Cloud U D v u j k A) :
    Cloud (fun x z=> V x z • U x z) D v u j (n+k) (C*A*3^j) := by
  refine ⟨h.toPicture.mix he.toPicture, fun y hy z=> (Trace.paint (h.view _ hy z) (he.view _ hy z)).climb ?_ le_rfl, fun R hR=> ?_⟩
  · unfold vat; apply le_of_eq; ring
  obtain ⟨d,hd,Q,hQ⟩:=h.satellite R hR; obtain ⟨d',hd',Q',hQ'⟩:=he.satellite R hR
  exact ⟨min d d',lt_min hd hd', _ ,(hQ.mend le_rfl (min_le_left ..) le_rfl le_rfl).mix (hQ'.mend le_rfl (min_le_right ..) le_rfl le_rfl)⟩
lemma cloud_prod {β : Type} (s : Finset β) (f : β→ ℰ→ Ξ→ℝ) (a : β→ℝ) (d : β→ℕ)
    (hp : ∀ i∈s, Cloud (f i) D v u j (d i) (a i)) :
    Cloud (fun x z=> ∏ i∈s, f i x z) D v u j (∑ i∈s,d i) (∏ i∈s,(a i * 3^j)) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,Finset.prod_empty,norm_one] using! Cloud.still (E:=E) (ι:=ι) (1:ℝ) D v u j
  | insert i s hi ih =>
    simp_rw [sum_insert hi,prod_insert hi]
    rw [mul_right_comm (a i)]
    exact (hp i (Finset.mem_insert_self ..)).mix (ih fun i hi=> hp i (Finset.mem_insert_of_mem hi))

lemma powerCloud (hv : v≤1) (D u : ℝ) (i j : ℕ) : Cloud (fun (x:ℰ) (_:Ξ)=> x.1^i) D v u j 0 ((3^j)^i) := by
  have he D v (hv : v≤1) : Picture (fun (x:ℰ) (_:Ξ)=> x.1^i) D v u j ((3^j)^i):= ⟨by positivity,fun x _=> stronglyMeasurable_const.indicator measurableSet_closedBall, fun x hx _ _=> Trace.axisPower (((patch_test ..).1 hx).1.le.trans hv)⟩
  exact ⟨he D v hv, fun x _ z=> by rw [vat,pow_zero,mul_one]; exact Trace.axisPower (q:=(0,x)) (by simp), fun R _=>⟨1,zero_lt_one,_,he R 1 le_rfl⟩⟩

lemma Picture.exponents (h : Picture V D v u j C) (hA:0 ≤ A) (hf : ∀ x∈patch E v u, ∀ z,‖z‖≤D → Brush j A 1 Real.exp (V x z)) :
    Picture (fun x z=> Real.exp (V x z)) D v u j (clump j C A) := by
  have hC:=h.expense
  refine ⟨by unfold clump; positivity,fun x hx=> ?_,fun x hx z hz=> composite (g:=Real.exp) (h.budget x hx z hz) (hf x hx z hz)⟩
  let s:=closedBall (0:Ξ) D
  rw [show s.indicator (fun z=> Real.exp (V x z))= s.indicator (Real.exp ∘ velvet V D x) from funext fun i=>by by_cases H:i∈s <;> simp [Set.indicator,velvet,H,s] at *]
  exact (Real.continuous_exp.comp_stronglyMeasurable (h.cut x hx)).indicator measurableSet_closedBall
lemma clump_stairs (hc : 1 ≤ B) (hp : 0 ≤ C) (he : 0 ≤ A) (j : ℕ) :
    clump j (C*B) A ≤ clump j C A*B^j:= by
  unfold clump; rw [mul_assoc ((Nat.factorial j:ℝ)*A), ← mul_pow]; gcongr; linarith
lemma Cloud.exponents (h : Cloud V D v u j k C) (he : ∀ x∈patch E v u, ∀ z,‖z‖≤D → ‖V x z‖ ≤ 1)
    (hA : ∀ i∈Set.Icc (-1:ℝ) 1, Brush j A 1 Real.exp i) (hc : ∀ x : E,‖x‖<u→ ∀ z, |V (0,x) z|≤1) :
    Cloud (fun x z=> Real.exp (V x z)) D v u j (k*j) (clump j C A) := by
  have hQ:= (hA 1 (by simp)).nonneg
  refine ⟨h.toPicture.exponents hQ (fun x hx z hz=> hA _ (abs_le.mp (he _ hx _ hz))),fun x hx z=> ?_, fun R hR=>?_⟩
  · apply (composite (h.view x hx z) (hA _ (abs_le.mp (hc _ hx z)))).climb _ le_rfl
    unfold vat; rw [pow_mul]; exact clump_stairs (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))) h.expense hQ j
  obtain ⟨v',hv,A',h'⟩:= h.satellite R hR
  obtain ⟨J,hJ,hX⟩:= Brush.compact (s:=Set.Icc (-A') A') (k:=j) (f:=Real.exp) isCompact_Icc (fun i _=> Real.contDiff_exp.contDiffAt)
  exact ⟨v',hv,_,h'.exponents hJ.le (fun x hx z hz=> hX _ (abs_le.mp (h'.budget x hx z hz).bound))⟩
end YM.RemainderComparison.Germ
