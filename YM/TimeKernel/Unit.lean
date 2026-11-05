import YM.TimeKernel.Trace


/-!
# Pass to actual cyclic integral difference

Read replica column strengths `Tr ((BᴴB)^p)`. Lower bound Z *actual*,
so eventual finite approximants' norms see no zero. No ground-state assumption.
-/
set_option autoImplicit false
noncomputable section
namespace YM.TimeKernel
open Filter Function Set Analysis Matrix MeasureTheory
open scoped Topology BigOperators ComplexOrder InnerProductSpace
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {n : ℕ}

def along (T : K X) (B : Fin n → K X) (Y : Fin n → ℕ) :=
    (List.ofFn fun i => B i::List.replicate (Y i) T).flatten

def multiply (B : K X) (p : ℕ) := (List.replicate p [op B,B]).flatten

variable (T : K X)

omit [IsFiniteMeasure μ] in
lemma purchased (B : Fin n → K X) (Y : Fin n → ℕ) (P : Quad X) :
    List.prod ((along T B Y).map (sample μ P)) = Holder.combine (fun i => sample μ P (B i) * (sample μ P T)^Y i) := by
  induction n with
  | zero => simp [Holder.combine,along]
  | succ n ih =>
    rw [show along T B Y=(B 0::List.replicate (Y 0) T)++along T (Fin.tail B) (Fin.tail Y) by
      simp only [along,List.ofFn_succ,List.flatten_cons];rfl]
    rw [List.map_append,List.prod_append, ih, Holder.stem]
    simp only [List.map_cons,List.prod_cons,List.map_replicate,List.prod_replicate]
    rfl

omit [IsFiniteMeasure μ] in
lemma column (B : K X) (p : ℕ) (Q : Quad X) : ((multiply B p).map (sample μ Q)).prod =
    ((sample μ Q B)ᴴ * sample μ Q B)^p := by
    simp [multiply,← oriented]

variable [MetricSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X]

abbrev possible (k : K X) := Continuous (Function.uncurry k)

lemma goes (H : possible T) (B : Fin n → K X) (h : ∀ i, possible (B i)) (Y : Fin n → ℕ) [Nonempty (Fin n)] :
    Tendsto (fun k => (Holder.combine (fun i => sample μ (Quad.shrink X k) (B i) * sample μ (Quad.shrink X k) T ^ Y i)).trace) atTop
      (𝓝 (closed μ (along T B Y))) := by
  simp_rw [← purchased]
  apply learns μ
  · let i : Fin n := Classical.ofNonempty
    have he : B i∈along T B Y := List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_cons_self⟩
    exact List.ne_nil_of_mem he
  intro K hk
  obtain ⟨k,hk,he⟩ := List.mem_flatten.mp hk
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
  rcases List.mem_cons.mp he with e|e
  · subst K; exact h i
  rw [(List.mem_replicate.mp e).2]; exact H

lemma totality (B : K X) (h : possible B) {p : ℕ} (hp : 0<p) :
    Tendsto (fun k => Holder.paysNorm p (sample μ (Quad.shrink X k) B)) atTop (𝓝 (‖closed μ (multiply B p)‖^(Holder.rate p))) := by
  have hh := learns μ (multiply B p) (show multiply B p ≠ [] by
    cases p with
    | zero => simp at hp
    | succ p => simp [multiply,List.replicate_succ]) (fun i hi => ?_)
  simp_rw [column] at hh
  exact hh.norm.rpow_const (Or.inr ((inv_pos.mpr (Nat.cast_pos.mpr (show 0<p+p by omega))).le))
  obtain ⟨z,hz,hy⟩ := List.mem_flatten.mp hi
  rw [(List.mem_replicate.mp hz).2] at hy
  rcases List.mem_cons.mp hy with e|e
  · rw [e]; exact continuous_star.comp (h.comp continuous_swap)
  rw [List.mem_singleton.mp e]; exact h

/-- Uniform Lipschitz engine using column bounds on the SAME underlying
kernels. Compare two lists of integer gaps differing by one center motion. -/
theorem passage (B : Fin n → K X) (h : NNKernel T) (hc : possible T) (ht : ∀ i, possible (B i)) {width N p m : ℕ}
    (he : N=(p+p)*width) (hp : 0 < p) (hw : 0 < width) (R : ℝ) (hr : 0 < R) (hR : closed μ (List.replicate N T) = ↑R)
    {Y Z : Fin n → ℕ} (hY : n*width+∑ i, Y i=N)
    (i j : Fin n) (hij : i≠j) (hu : Y i+m=Z i) (hv : Z j+m=Y j)
    (hm : ∀ a : Fin n, a≠i → a≠j → Y a=Z a)
    (r : ℝ) (hy : 0<r) (hO : ∀ i : Fin n, 2*r < Y i) (hs : (m:ℝ) ≤ r)
    (K : Fin n → ℝ) (hK : ∀ i, ‖closed μ (multiply (B i) p)‖^(Holder.rate p) ≤ K i * R ^ (Holder.rate p)) :
    ‖closed μ (along T B Z)-closed μ (along T B Y)‖ ≤ R*(∏ i, K i)/r * m := by
  letI : Nonempty (Fin n) := ⟨i⟩
  have hZ : 0<N := by rw [he]; positivity
  let P := Quad.shrink X
  have ha := learns μ (List.replicate N T) (by simp [hZ.ne']) fun i hi => (List.mem_replicate.mp hi).2 ▸ hc
  simp_rw [List.map_replicate, List.prod_replicate,hR] at ha
  have hl : Tendsto (fun x : ℕ => Holder.Q (sample μ (P x) T) N) atTop (𝓝 R) := by
    unfold Holder.Q; simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,P] using ha.norm
  let A (k : ℕ) (v : Fin n → ℕ) := (Holder.combine (fun i => sample μ (P k) (B i) * sample μ (P k) T ^ (v i : ℕ))).trace
  let D (k : ℕ) := Holder.cost (sample μ (P k) T) (fun i => sample μ (P k) (B i)) p N
  have hq : ∀ᶠ k : ℕ in atTop, ‖A k Z-A k Y‖ ≤ D k / r * m := (hl.eventually (lt_mem_nhds hr)).mono
    (fun x hx => Holder.finite_lip (safe μ _ _ h) _ he hp hw hx hY i j hij hu hv hm r hy hO hs)
  let f (i : Fin n) := ‖closed μ (multiply (B i) p)‖^(Holder.rate p)
  have h' : Tendsto D atTop (𝓝 ((∏ i, f i) * R ^ ((1:ℝ) - n*Holder.rate p))) :=
    (tendsto_finsetProd Finset.univ (fun i _ => totality μ _ (ht i) hp)).mul (hl.rpow_const (Or.inl hr.ne'))
  apply le_trans (le_of_tendsto_of_tendsto ((goes μ T hc _ ht Z).sub (goes μ T hc _ ht Y) |>.norm)
    ((h'.div_const _).mul_const _) hq)
  have hx := Finset.prod_le_prod (s := Finset.univ) (f := f) (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun i _ => hK i)
  let a := Holder.rate p
  refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ hy.le) (Nat.cast_nonneg _)
  apply le_trans (mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (x := R) hr.le (1 - n*a))) (le_of_eq ?_)
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ, ← Real.rpow_mul_natCast hr.le,mul_assoc,← Real.rpow_add hr]
  rw [Fintype.card_fin,show Holder.rate p*↑n+(1-n*a) =1 by unfold a;ring]; simp [mul_comm]
end YM.TimeKernel
