import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Matches
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Range
/-!
 # A general track preserves Regular under localization. Mover derivatives
 mixed LR, converted only at the given configuration: use also when Fashion
 builds replicas, thus no naive assigning forward derivatives to inverse links.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Local Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {C c : Side} {B:BudgetPoint} (A:Track C) {q : ℝ} (o:Site c) {f:Config G C→ℝ}
lemma modeling (V:Config G c) (l : Bond C): ContDiffAt ℝ ω (fun x => G.mat (shape A o (increment V x) l)) 0:= by
  unfold shape increment; split_ifs
  · simp only [G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
  · simp only [G.mat_inv,G.mat_mul]; exact ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const)).contDiffAt
  exact contDiffAt_const
lemma cloth (V:Config G c) (h:Chart B.order f (shape A o V)): Chart B.order (f∘shape A o) V:= by
  apply chart_comp (k:=B.order) (x:=(0:Directions G c)) (W:=fun v=> shape A o (increment V v)) ?_ (modeling A o V); rw [Work.G07.at_zero_increment]; exact h
lemma regular {Z:Support c} (h:B.Regular univ f) (he:∀ i,sites A o i∈Z) : B.Regular Z (f∘shape A o):= by
  have hh (U) (hp:Healthy B.threshold Z U) : Chart B.order (f∘shape A o) U:= cloth A o U (h.smooth _ (by unfold Healthy; rw [Slide.allFlag A o U Z he B.threshold B.threshold_pos.le hp]; simp))
  refine ⟨fun x y hi=> congr_arg f (stable A o Z he x y hi), h.borel.comp ?_, fun z U=> by simp only [Function.comp_apply]; rw [shape_gauge,h.symmetry], hh,fun U hu c l hl=> left_has c hl (hh U hu)⟩
  have hv:Continuous (shape (K:=G.El) A o):= continuous_pi fun i=> by unfold shape; split_ifs<;> fun_prop
  exact hv.measurable
-- A move at a fixed edge (both visits only), not reading the fine extension.
def move (v:Directions G c) : LR G C := ((fun i=> if grade A i=1 then v (sites A o i.1,i.2) else 0),fun i=> if grade A i= -1 then -v (sites A o (i.1+step i.2),i.2) else 0)
lemma going (V:Config G c) (v: Directions G c) (t:ℝ): shape A o (increment V (t • v))= mix (shape A o V) (t • move A o v):= by
  funext ⟨x,i⟩; rcases graded A (x,i) with h|h|h <;> simp [shape,h,move, mix, increment, Work.F03.exp_neg_color]
lemma raced (f: Config G C→ℝ) (l:List (Directions G c)) (V:Config G c) : leftDerivs (f∘shape A o) l V=mixJets f (l.map (move A o)) (shape A o V):= by
  induction l generalizing V with
  | nil=>rfl
  | cons i l ih=> simp only [leftDerivs,List.map_cons, mixJets, ih, going]
private lemma list_wage {ι:Type} (l : List ι) (f:ι→ℝ) (h : ∀ i∈l,‖f i‖≤q): ‖(l.map f).sum‖ ≤ (l.length:ℝ)*q:= by
  induction l with
  | nil=> simp
  | cons i l ih=> simp only [List.map_cons,List.length_cons,List.sum_cons,Nat.cast_add,Nat.cast_one,add_mul, one_mul,add_comm (_* q) q]; exact (norm_add_le ..).trans (add_le_add (h i (by simp)) (ih (fun i hi=> h i (List.mem_cons_of_mem _ hi))))
lemma stalled (f:Config G C→ℝ) {b:ℕ} (he:∀ i,separation o (sites A o i)≤ b) (l:List (Directions G c)) (V:Config G c) (hp: l.length≤B.order) (hD:∀ v∈l,B.dirBound o v)
   (hc:Chart B.order f (shape A o V)) (hm : ∀ i:List (Directions G C),i.length≤ B.order→ (∀ v∈i, ‖v‖ ≤ B.threshold) → ‖leftDerivs f i (shape A o V)‖ ≤ q):
    ‖leftDerivs (f∘shape A o) l V‖ ≤ 2^B.order*((1+(b:ℝ))^(B.power*B.order))*q:= by
  let X:= (1+(b:ℝ))^B.power; let v:=shape A o V; let y:= l.map (move A o); let e:=convertOrder v y
  have hx:1≤X:=one_le_pow₀ (by simp)
  have hj (z) (hz:z∈l) i k: ‖z (sites A o i,k)‖≤ X*B.threshold := by
    apply (hD _ hz _).trans; rw [mul_comm X]; apply mul_le_mul_of_nonneg_left _ B.threshold_pos.le; apply pow_le_pow_left₀ (by positivity) _ _; gcongr; rw [separation_comm]; exact_mod_cast he i
  have h p (hh:p∈y): ‖p.1‖≤X*B.threshold ∧ ‖rotateRight v p.2‖≤ X*B.threshold:= by
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hh; have hX := mul_nonneg (zero_le_one.trans hx) B.threshold_pos.le; constructor
    · apply (pi_norm_le_iff_of_nonneg hX).2; intro i; dsimp only [move]; split; exact hj z hz _ _; simp only [norm_zero]; exact hX
    apply (pi_norm_le_iff_of_nonneg hX).2; intro i; dsimp only [rotateRight,move]; rw [G.norm_adjoint]; split; next ht=> rw [norm_neg]; exact hj z hz _ _
    simp only [norm_zero]; exact hX
  have hz:=convert_mem v (fun i=>‖i‖≤ X*B.threshold) y h
  have hs : y.length=l.length:= List.length_map _
  have hw i (hi:i∈e): ‖leftDerivs f i v‖≤ X^l.length*q:= by
    obtain ⟨hk,hh⟩:=hz i hi; let d:=i.map fun i=> X⁻¹ • i
    have hx':0<X:=zero_lt_one.trans_le hx
    have h : d.length=l.length := (List.length_map _|>.trans (hk.trans hs))
    have hE:‖leftDerivs f d v‖ ≤ q:= by
      apply hm d (h.trans_le hp); intro j hj; obtain ⟨j,hj',rfl⟩:= List.mem_map.mp hj; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hx'.le)]; apply (mul_le_mul_of_nonneg_left (hh _ hj') (inv_nonneg.mpr hx'.le)).trans_eq; field_simp
    have hd : d.map (fun i=> X • i)=i:= by simp [d,List.map_map,Function.comp_def,smul_smul,hx'.ne']
    conv_lhs => rw [← hd,March.expands, h, norm_smul,Real.norm_of_nonneg (pow_pos hx' _).le]
    exact mul_le_mul_of_nonneg_left hE (pow_nonneg hx'.le _)
  rw [raced A o]; change ‖mixJets f y v‖ ≤ _; rw [mix_convert v y f ?_ hc (hs.trans_le hp)]; swap
  · intro p hv q h i; obtain ⟨z,hz,rfl⟩:= List.mem_map.mp hv; obtain ⟨u,hu,rfl⟩:= List.mem_map.mp h; rcases graded A i with h|h|h<;> simp [move,h]
  have ht:0 ≤ q:= le_trans (norm_nonneg _) (hm [] (by simp) (fun i hi=>False.elim (List.not_mem_nil hi)))
  refine (list_wage _ _ hw).trans ?_
  rw [convert_length,hs,Nat.cast_pow,Nat.cast_ofNat, ← mul_assoc,pow_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (pow_le_pow_right₀ (by norm_num) hp) (pow_le_pow_right₀ hx hp) (pow_nonneg (zero_le_one.trans hx) _) (by positivity)) ht

section recolor
variable {V:Config G C} (u:Site C→ G.El) (h : GaugeInvariant f)
abbrev plume (A: Directions G C) : Directions G C:=fun i=> G.adjoint (u i.1) (A i)
include h
lemma traced (l:List (Directions G C)): leftDerivs f (l.map (plume u)) (gauge u V)=leftDerivs f l V:= by
  induction l generalizing V with
  | nil=>exact h ..
  | cons a l ih=>
    simp only [leftDerivs,List.map_cons]; apply congr_arg (fun f:ℝ→ℝ=> deriv f 0); funext t; rw [show increment (gauge u V) (t • Slide.plume u a)=gauge u (increment V (t • a)) from ?_]; exact ih
    funext i; unfold increment Lattice.gauge plume; simp only [Pi.smul_apply,← map_smul, Channel.exp_adjoint]; group
lemma bills {p : ℕ} {b:ℝ} (hM:∀ l:List (Directions G C), l.length≤p→(∀ i∈l, ‖i‖≤b)→ ‖leftDerivs f l (gauge u V)‖≤q) (l: List (Directions G C)) (hl:l.length≤p) (hx:∀ i∈l,‖i‖≤b):
    ‖leftDerivs f l V‖≤q := by
  rw [← traced u h]; refine hM _ (by simpa) fun i hi=> ?_; obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hi; apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hx a ha))).2; intro i; unfold plume; rw [G.norm_adjoint]; exact (norm_le_pi_norm _ _).trans (hx a ha)
end recolor
end YM.PhysicalNext.Repeat.Slide
