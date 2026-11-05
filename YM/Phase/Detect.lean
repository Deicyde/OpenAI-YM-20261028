import YM.Cells.Corrected
import YM.Ground.Spectrum


/-!
# Actual finite projections: power moments on the whole corrected operators
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction.Retain
open Function Set Filter MeasureTheory Measure
open Table Cells CellHyp OS Ground Wilson Word
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators ContDiff
variable {G : Gauge}
section Bit
variable {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)
variable {R : P.Resolution}

/-- spectral shortcut for moment bounds to all characters, against probability
measure with actual full support. -/
abbrev Tall (x : P.algebra) (t : ℝ) := ∀ n : ℕ, (inner ℂ V.omega0 ((((star x*x)^n:P.algebra).val) V.omega0)).re ≤ t^(2*n)
lemma bit (H : R.Out) (x : P.algebra) (t : ℝ) (ht : 0 ≤ t) (h : Tall P x t) (i : R.X) :
    ‖R.character i x‖ ≤ t := by
  classical
  have ht' (j n) : R.character j (((star x*x)^n:P.algebra))=(↑(‖R.character j x‖^(2*n)):ℂ) := by
    rw [map_pow,map_mul,map_star,pow_mul,Complex.ofReal_pow -- direction
        ]
    congr 1
    change starRingEnd ℂ _ * _=_
    rw [mul_comm, Complex.mul_conj,Complex.normSq_eq_norm_sq]
  let f (i) := ‖R.character i x‖
  have hg n : (∫ i, f i^(2*n) ∂R.μ) ≤ t^(2*n) := by
    have he := h n; rw [← H.ground] at he
    simp_rw [ht',integral_complex_ofReal,Complex.ofReal_re] at he; exact he
  by_contra! hv
  obtain ⟨p,hp,hv⟩ := exists_between hv
  let Q := {x | p<f x}
  have he : Continuous f := (H.weak x).norm
  have hu : IsOpen Q := isOpen_lt continuous_const he
  have ho := H.support; have h' := H.normalized
  let c := R.μ.real Q
  have hc : 0<c := by apply ENNReal.toReal_pos (mu_ne ho Q hu ⟨i,hv⟩) (measure_ne_top R.μ Q)
  have hz := ht.trans_lt hp
  have hf n : c ≤ ((t/p)^2)^n := by
    let g (i) := f i ^ (2*n)
    have hx : Integrable g R.μ := (he.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← pow_mul,div_pow]
    refine (le_div_iff₀ (pow_pos hz _)).2 ?_
    calc
      _ = ∫ _ in Q,(p^(2*n):ℝ) ∂R.μ := by simp [c]
      _ ≤ ∫ i in Q,g i ∂R.μ := setIntegral_mono_on (integrable_const _) hx.integrableOn hu.measurableSet fun j hj =>
          pow_le_pow_left₀ hz.le (show p < f j from hj).le _
      _ ≤ ∫ i, g i ∂R.μ := setIntegral_le_integral hx (ae_of_all _ fun i => pow_nonneg (norm_nonneg _) _)
      _ ≤ t^(2*n) := hg n
  have hq : t/p < 1 := div_lt_one hz |>.2 hp
  have hx := div_nonneg ht hz.le
  exact hc.not_ge (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) (by exact pow_lt_one₀ hx hq (by omega))) hf)
where mu_ne (h : R.μ.IsOpenPosMeasure) (q : Set R.X) (a : IsOpen q) (b : q.Nonempty) : R.μ q≠0 := IsOpenPosMeasure.open_pos q a b
end Bit
variable {C : Family G} {S : Table C.book} {V : Chamber S timeAxis} {d : ℕ} {X : Columns C S d}
variable {f : Order} (Y : X.Trials) (Q : Y.Valid f) (P : Spread V) (a : P.Resolution)

def token (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : C.book.Token := ⟨d,Y.later k (Columns.Trials.names (X := X) i c s)⟩
def plant (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : C.book.Plant := (Y.realPlace k i s, token Y k i c s)
include Q in
lemma apart (k i c s u) (h : s<u) : distinct [plant Y k i c s,plant Y k i c u] := by
  suffices he : (plant Y k i c s).1≠(plant Y k i c u).1 from locations.mpr (by simp [he])
  intro hp
  exact h.ne ((show Injective _ from generic_conf _ (Q.generic k i)) hp)
-- include Q needed above

abbrev atOne (p : C.book.Plant) := M P [p] (locations.mpr (by simp))
def Δone (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) (s : Fin ((X.row i).extra+1)) : P.algebra := atOne P (plant Y k i c s)- Y.singleton k i c s • 1

def Δtwo (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) (s u : Fin ((X.row i).extra+1)) (h : s<u) : P.algebra := M P _ (apart Y Q k i c s u h)-
    Y.singleton k i c s • atOne P (plant Y k i c u) - Y.singleton k i c u • atOne P (plant Y k i c s)+
    (Y.singleton k i c u *Y.singleton k i c s-Y.cumulant k i c s u) • 1

/-- Need trains alternating translated (θ or conjugate after Mθ bridge),
all positions generic, including all cross copies. Maps exactly rankwid tail. -/
structure Funds : Prop where
  one (k i c s) : Tall P (Δone Y P k i c s) (Y.gap k)
  pair (k i c s u) (h : s<u) : Tall P (Δtwo Y Q P k i c s u h) (Y.gap k)
variable (H : Funds Y Q P)

lemma pops {D : Table C.book} {i} (h : a.receives D i) (u : C.book.Word) (hu : distinct u) :
    a.character i (M P u hu)=D.expect u := (h u hu _ _ (Spread.Resolution.place_exists hu).choose_spec.choose_spec).symm

lemma picky (j) (x : ℂ) (p : P.algebra) : a.character j (x • p)=x*a.character j p := (a.character j).toAlgHom.toLinearMap.map_smul _ _ 
lemma plus (j) (x y : P.algebra) : a.character j (x+y) = a.character j x+a.character j y := (a.character j).toAlgHom.map_add x y
lemma minus (j) (x y : P.algebra) : a.character j (x-y) = a.character j x-a.character j y := (a.character j).toAlgHom.map_sub x y
include H in
lemma one_near (hi : a.Out) {D : Table C.book} {v} (h : a.receives D v) k i c s :
    ‖D.expect [plant Y k i c s]- Y.singleton k i c s‖ ≤ Y.gap k := by
  have H := bit P hi _ _ (Y.allowed k) (H.one k i c s) v
  rw [Δone,minus P a v,picky P a v,atOne,pops P a h,map_one] at H; simpa only [smul_eq_mul,mul_one] using H

def free2 (k : ℕ) (i : Fin X.amount) (c : Fin (X.dim+1)) (s u : Fin ((X.row i).extra+1)) := Y.cumulant k i c s u + Y.singleton k i c s* Y.singleton k i c u

include H in
lemma pair_near (hi : a.Out) {D : Table C.book} {v} (h : a.receives D v) k i c s u (hp : s<u) :
    ‖D.expect [plant Y k i c s,plant Y k i c u]- free2 Y k i c s u‖ ≤
      Y.gap k+ (‖Y.singleton k i c s‖+‖Y.singleton k i c u‖)*Y.gap k := by
  have hb := bit P hi _ _ (Y.allowed k) (H.pair k i c s u hp) v
  have hy (x) := one_near Y Q P a H hi h k i c x
  let U := D.expect
  let y t := plant Y k i c t
  let j t := Y.singleton k i c t
  rw [Δtwo,plus P a v,minus P a v,minus P a v,picky P a v,picky P a v,picky P a v,map_one] at hb
  simp only [mul_one,atOne,pops P a h] at hb
  let G (s t) := U [y s,y t]-j s*U [y t]-j t*U [y s]+(j t*j s-Y.cumulant k i c s t)
  change ‖U _-_‖ ≤ _
  rw [show U [y s,y u]- _= G s u + (j s*(U [y u]-j u)+j u*(U [y s]- j s)) from by unfold G; unfold free2; simp only [j]; ring]
  rw [add_mul]
  refine (norm_add_le ..).trans (add_le_add hb ((norm_add_le ..).trans ?_))
  rw [norm_mul,norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_left (hy u) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (hy s) (norm_nonneg _))
end YM.Extraction.Retain
