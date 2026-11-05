import YM.Push.LOOP_COEFFICIENT.Paths.Lead
import YM.Push.LOOP_COEFFICIENT.Tubes

/-!
# Matrix calculus for leading rooted symbols
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Continuum
open Matrix Paths Function Set Filter Lattice Laurent RG Bloch Wilson  Complex Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c] {n m : ℕ}
  {F : ℂ → Matrix a b ℂ} {X : Matrix a b ℂ}

omit [DecidableEq a] in
lemma lead_entry (h : Lead n F X) (i j) : Lead n (fun t => F t i j) (X i j) := h.map ((entryLinearMap ℂ ℂ i j : Matrix a b ℂ →ₗ[ℂ] ℂ).toContinuousLinearMap)
omit [DecidableEq a] in
lemma lead_matrix (h : ∀ i j, Lead n (fun t => F t i j) (X i j)) : Lead n F X := by
  choose g hg hh H using h
  refine ⟨fun t => of fun i j => g i j t,analyticMatrix (by exact hg),Matrix.ext hh,(eventually_all.mpr (fun i => eventually_all.mpr (H i))).mono fun t ht => Matrix.ext (ht)⟩

omit [DecidableEq a] in
lemma lead_paired (h : Lead n F X) (x y) : Lead n (fun t => x ⬝ᵥ F t *ᵥ y) (x ⬝ᵥ X *ᵥ y) := h.map ((show Matrix a b ℂ →ₗ[ℂ] ℂ from {
    toFun M := x ⬝ᵥ M *ᵥ y
    map_add' m n := by rw [Matrix.add_mulVec,dotProduct_add]
    map_smul' c m := by rw [Matrix.smul_mulVec,dotProduct_smul]; rfl }).toContinuousLinearMap)
omit [DecidableEq a] in
lemma lead_times {H : ℂ → Matrix b c ℂ} {Y : Matrix b c ℂ} (hf : Lead n F X) (hg : Lead m H Y) : Lead (n+m) (fun t => F t * H t) (X*Y) := lead_matrix (fun i j => Lead.sum Finset.univ fun k _ => (lead_entry hf i k).mul (lead_entry hg k j))


variable {R S : Vertex d a b}
structure Germ₁ (R S : Vertex d a b) : Prop where
  first q : Lead 1 (fun t => R.base (t • q)) (S.base q)
  second q p v : Lead 0 (fun t => R.one (t • q) (t • p) v) (S.one q p v)
  third q p s v w : ContDiffAt ℂ ω (fun t : ℂ => R.two (t • q) (t • p) (t • s) v w) 0
  truncate : S.two=0
namespace Germ₁

end Germ₁

structure Germ₂ (R S : Vertex d a b) : Prop where
  base q : Lead 2 (fun t => R.base (t • q)) (S.base q)
  one q p v : Lead 1 (fun t => R.one (t • q) (t • p) v) (S.one q p v)
  two q p s v w : Lead 0 (fun t => R.two (t • q) (t • p) (t • s) v w) (S.two q p s v w)

omit [DecidableEq a] in
lemma Germ₁.mul {U V : Vertex d b c} (h : Germ₁ R S) (h' : Germ₁ U V) : Germ₂ (R.mul U) (S.mul V) := by
  refine ⟨fun q => lead_times (h.first q) (h'.first q),fun q p v => ?_,fun q p s v w => ?_⟩
  · simpa only [smul_add] using! ((lead_times (h.first (q+p)) (h'.second q p v)).add (lead_times (n:=0) (m:=1) (h.second q p v) (h'.first q)))
  · simp only [Vertex.mul,LinearMap.add_apply,LinearMap.compr₂_apply,LinearMap.compl₁₂_apply,LinearMap.flip_apply,matrixMulLinear,LinearMap.mk₂_apply,h.truncate,h'.truncate,Pi.zero_apply,LinearMap.zero_apply,Matrix.mul_zero,Matrix.zero_mul,← smul_add]
    convert! ((((lead_times ((h.first (q+p+s)).lower (m:=0) (by decide)) (lead_zero (h'.third q p s v w))).add (lead_times (h.second (q+s) p v) (h'.second q s w))).add (lead_times (h.second (q+p) s w) (h'.second q p v))).add (lead_times (lead_zero (h.third q p s v w)) ((h'.first q).lower (m:=0) (by decide)))) using 1; simp
omit [DecidableEq a] in lemma Germ₂.add {U V : Vertex d a b} (h : Germ₂ R S) (h' : Germ₂ U V) : Germ₂ (R.add U) (S.add V) := ⟨fun _ => (h.base _).add (h'.base _),fun _ _ _ => (h.one ..).add (h'.one ..),fun _ _ _ _ _ => (h.two ..).add (h'.two ..)⟩
end YM.Push.Loops.Continuum
