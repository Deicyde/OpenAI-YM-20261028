import YM.OS.Slabs

/-!
# Dyadic trains actual expectations to bounded slab existence

Forward T acts dense; show powers for all **finite polynomials** from point
inputs, don't require exterior constant independent of those probes. C currently positive.
No starting postulate of bounded T or bounded eval at boundary.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Analysis Word Function Set Filter
open scoped Topology NNReal InnerProductSpace ContDiff BigOperators

/-! Scaling lemma works pure Gram. Useful also for resolution. -/
namespace Drive
variable {V : Type*} [AddCommMonoid V] [Module ℂ V] {H : Hilbert}

lemma against (A B : V→ₗ[ℂ] V) (X : V →ₗ[ℂ] H) (D : ℝ) (h : 0<D)
    (hp : ∀ v w, inner ℂ (X (A v)) (X w)=inner ℂ (X v) (X (B w)))
    (ht : ∀ v:V, ∃ C : ℝ, ∀ n:ℕ, ‖X (((B ∘ₗ A)^n) v)‖ ≤ C*D^(2*n)) (v : V) :
    ‖X (A v)‖ ≤ D*‖X v‖ := by
  let T : V→ₗ[ℂ] V := B ∘ₗ A
  have hh (v w) : inner ℂ (X v) (X (T w))=inner ℂ (X (T v)) (X w) := by
    change inner ℂ (X _) (X (B _))=_
    rw [← hp,← inner_conj_symm (X (A v)),hp,inner_conj_symm];rfl
  have hw n (v w) : inner ℂ (X v) (X ((T^n) w))=inner ℂ (X ((T^n) v)) (X w) := by
    induction n generalizing v w with
    | zero => rfl
    | succ n ih =>
      conv_rhs => rw [pow_succ]
      conv_lhs => rw [pow_succ']
      rw [show (T*T^n) w=T ((T^n) w) from rfl, hh, ih];rfl
  obtain ⟨C,hC⟩ := ht v
  let d n := ‖X ((T^n) v)‖/D^(2*n)
  have Ht n : 0 ≤ d n := by unfold d; positivity
  have he : BddAbove (range d) := by
    refine ⟨C, fun c he => ?_⟩; obtain ⟨i,rfl⟩ := he
    exact (div_le_iff₀ (pow_pos h _)).2 (hC _)
  let s := ⨆ i, d i
  have hr n : d n≤s := le_ciSup he _
  have hz n : d n ^ 2 ≤ ‖X v‖ * s := by
    have hi : ‖inner ℂ (X v) (X ((T^(n+n)) v))‖= ‖X ((T^n) v)‖^2 := by
      rw [pow_add,Module.End.mul_apply, hw,inner_self_eq_norm_sq_to_K]; simp
    calc _ = ‖inner ℂ (X v) (X ((T^(n+n)) v))‖/D^(2*(n+n)) := by unfold d; rw [hi,div_pow, Nat.mul_add, pow_add, pow_two (D^_)]
         _ ≤ ‖X v‖*d (n+n) := by
             apply (div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (pow_nonneg h.le _)).trans (le_of_eq ?_); unfold d; ring
         _ ≤ _ := by gcongr; exact hr _
  have hs := (Ht 0).trans (hr 0)
  have hu : s ≤ ‖X v‖ := by
    have hx : s ≤ √(‖X v‖*s) := ciSup_le fun i => (Real.le_sqrt (Ht i) (by positivity)).mpr (hz i)
    have he := Real.sq_sqrt (show 0 ≤ ‖X v‖*s by positivity)
    nlinarith [norm_nonneg (X v)]
  have hy : ‖X (A v)‖^2=‖inner ℂ (X v) (X ((T^1) v))‖ := by rw [pow_one,show X (T v)=X (B (A v)) from rfl,← hp];simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  rw [hy]
  have hr : ‖X ((T^1) v)‖ ≤ ‖X v‖*D^(2*1) := (div_le_iff₀ (pow_pos h _)).1 ((hr 1).trans hu)
  apply (norm_inner_le_norm _ _).trans
  exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans_eq (by ring)
end Drive

variable {G : Gauge} {L : Register G} (S : Table L)
variable {d : ℝ≥0} {w : L.Word} {a : Axis}

/-- No norm abstraction on A prior construct. -/
abbrev Up (h : Slab a d w) := Finsupp.lmapDomain ℂ ℂ (entering h)
def ride (h : Slab a d w) (t : Future L a) (q : ℕ) := (entering (mirrorsSlab h) ∘ entering h)^[q] t

def QRead (A : ℝ) (h : Slab a d w) := ∀ v : Future L a, ∃ B : ℝ, ∀ n : ℕ,
    ‖S.gram a (ride h v n).val (ride h v n).val‖ ≤ B*A^(4*n)

variable {S} (V : Chamber S a)

lemma enroll (h : Slab a d w) (H : S.Hierarchy) (p q : Voice L a) : inner ℂ (V.GNS.stems (Up h p)) (V.GNS.stems q) =
    inner ℂ (V.GNS.stems p) (V.GNS.stems (Up (mirrorsSlab h) q)) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single i c =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,inner_add_right,hf,hg]
    | single j s => simp [Kernel.Gram.stems,Up,inner_smul_left, inner_smul_right,V.GNS.measure, realignment h H.translations i j]

lemma fed (h : Slab a d w) (i : Future L a) (c : ℂ) (p : ℕ) :
    V.GNS.stems (((Up (mirrorsSlab h) ∘ₗ Up h) ^ p) (Finsupp.single i c))= c • V.GNS.plant (ride h i p) := by
  let B := Up (mirrorsSlab h) ∘ₗ Up h
  have he p : (B^p) (Finsupp.single i c)= Finsupp.single (ride h i p) c := by
    induction p with
    | zero => rfl
    | succ p hp => rw [pow_succ',Module.End.mul_apply,hp]; simp [B, Up,ride,iterate_succ_apply']
  rw [he]; simp [Kernel.Gram.stems]

theorem size {A : ℝ} (H : Slab a d w) (hv : S.Hierarchy) (ht : QRead S A H) (hA : 0<A) (v : Voice L a) :
    ‖V.GNS.stems (Up H v)‖ ≤ A*‖V.GNS.stems v‖ := by
  apply Drive.against (H := V.GNS.H) (Up H) (Up (mirrorsSlab H)) V.GNS.stems A hA (enroll V H hv) _ v
  intro v
  let L := (Up (mirrorsSlab H) ∘ₗ Up H)
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0,by simp⟩
  | add f g hf hg =>
    obtain ⟨B,hB⟩ := hf; obtain ⟨D,hD⟩ := hg
    refine ⟨B+D,fun n => ?_⟩; simp only [map_add, add_mul]
    exact (norm_add_le ..).trans (add_le_add (hB n) (hD n))
  | single i p =>
    obtain ⟨Q,hQ⟩ := ht i
    have hp : 0 ≤ Q := le_trans (norm_nonneg _) (show _ from by simpa using hQ 0) -- type
    refine ⟨‖p‖*√Q,fun n => ?_⟩
    rw [fed,norm_smul,mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    rw [sq_key V.GNS,V.GNS.measure]; apply (hQ n).trans
    rw [mul_pow,Real.sq_sqrt hp, ← pow_mul, show 2*n*2=4*n by omega]

theorem producer {A : ℝ} (H : Slab a d w) (hv : S.Hierarchy) (ht : QRead S A H) (hA : 0<A) :
    ∃ P : V.GNS.H.Op, ‖P‖ ≤ A ∧ ∀ i, P (V.GNS.plant i) = V.GNS.plant (entering H i) := by
  apply V.GNS.by_bound _ _ hA.le
  intro f
  exact (show _ from by
    rw [show Finsupp.linearCombination ℂ _ f = V.GNS.stems (Up H f) from by
      rw [Up, Kernel.Gram.stems,Finsupp.lmapDomain_apply,Finsupp.linearCombination_mapDomain];rfl]
    exact size V H hv ht hA f)
end YM.OS
