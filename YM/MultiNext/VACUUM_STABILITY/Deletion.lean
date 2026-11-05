import YM.MultiNext.VACUUM_STABILITY.BulkGas
import YM.MultiNext.VACUUM_STABILITY.Environs

set_option warningAsError false

/-!
# Uniform hard-core scalar stability on the true output torus

Absolute countable words, rooted log increment solving by eliminating a **site**. One tape works
for all weights/exponents here; in particular a restricted cluster sum just uses zero amplitudes.
This is our variant of E's second-log trees; we do *not* require claims about an
absolute graph expansion on all edges. All powers including repeats paid.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum.Cluster
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Corona
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type} {n : Side}

def cost (X : I → Support n) (M : ℕ) (a : ℝ) (f : I → ℝ) (i : I) := f i*Real.exp (a*coverNumber M (X i))

def siteUnit (M : ℕ) := (((M+M+1:ℕ):ℝ))^4

structure Thin (X : I → Support n) (M : ℕ) (a : ℝ) (f : I → ℝ) (c : ℝ) : Prop where
  ok : 0 ≤ a
  sane : 0 ≤ c
  val (i : I) : 0 ≤ f i
  cap : c ≤ 1/2
  entrance : siteUnit M * (2*c) ≤ 1
  hit : Ac.Hit X M f (a+1) c

namespace Thin
variable {X : I → Support n} {M : ℕ} {a c : ℝ} {f : I → ℝ}

lemma enlarges (h : Thin X M a f c) (i : I) : f i ≤ cost X M a f i := by
  unfold cost; apply le_mul_of_one_le_right (h.val i)
  exact Real.one_le_exp (mul_nonneg h.ok (by positivity))

lemma seat (Y : Support n) (h : Thin X M a f c) : (Y.card:ℝ) * (2*c) ≤ coverNumber M Y := by
  have hp : (Y.card:ℝ) ≤ coverNumber M Y * siteUnit M := by unfold siteUnit; exact_mod_cast pays Y M
  calc
    _ ≤ coverNumber M Y * siteUnit M * (2*c) := mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) h.sane)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_of_le_one_right (by positivity) h.entrance

lemma face_pay (h : Thin X M a f c) (x : Site n) (R : Support n) : SumBudget (fun i : BulkGas.Face X R x =>
    cost X M a f i.val * Real.exp ((X i.val).card*(2*c))) c := by
  let g (i) := if x ∈ X i then cost X M (a+1) f i else 0
  have hh : SumBudget g c := h.hit x
  have hg : SumBudget (fun i : BulkGas.Face X R x => g i.val) c := by
    refine ⟨fun i => hh.1 i.val, hh.2.1.subtype _,?_⟩
    exact (Summable.tsum_subtype_le g _ hh.1 hh.2.1).trans hh.2.2
  refine Absolute.compare hg (fun i => mul_nonneg ((h.val i.val).trans (h.enlarges _)) (Real.exp_pos _).le)
    fun i => ?_
  dsimp only [g,cost]; rw [if_pos i.property.1,mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (h.val _)
  apply Real.exp_monotone
  rw [add_mul,one_mul]; gcongr; exact h.seat _
end Thin

abbrev Chorus (I : Type) (n : Side) := Site n → Text I

namespace Chorus
variable (D : Chorus I n)

def tune := Text.bind D

def plays (u : I → ℂ) := ∑ x, (D x).lineSum u

def QuietBeyond (Y : Support n) := ∀ x, x ∉ Y → IsEmpty (D x).address

lemma finances (Y : Support n) (hy : D.QuietBeyond Y) {f : I → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, (D x).Fund f c) : D.tune.Fund f (Y.card*c) := by
  let g x := if x ∈ Y then c else 0
  have he : SumBudget g (Y.card*c) := by
    refine ⟨fun x => by simp [g,ite_nonneg hc],(hasSum_fintype _).summable,?_⟩
    unfold g; rw [tsum_fintype,sum_ite_mem]; simp
  refine Text.bind_fund D he fun i => ?_
  unfold g; split
  · exact h _
  rename_i hx
  have := hy _ hx
  simp [Fund,SumBudget]

lemma tunes {f : I → ℝ} {c : ℝ} (h : D.tune.Fund f c) {u : I → ℂ} (hu : ∀ i, ‖u i‖ ≤ f i) :
    D.tune.lineSum u = D.plays u := by
  unfold tune; rw [Text.bind_sum D h hu,tsum_fintype]; rfl

lemma sticky (Y : Support n) (h : D.QuietBeyond Y) {X : I → Support n} {M : ℕ}
    (hP : ∀ x, (D x).Peaked X M x) : D.tune.Sticky X M Y := by
  intro i Z hz
  by_cases hh : i.1 ∈ Y
  · exact ((hP i.1).sticky hh) i.2 _ hz
  exact False.elim ((h i.1 hh).false i.2)
end Chorus

/-- Solves the exact ratio identity for all complex tests, anchored plates
and *absolute word mass*, paying the sum of covers (repeats charged). -/
structure Peeling (X : I → Support n) (R V : Support n) (D : Chorus I n) : Prop where
  roots : ∀ M x, (D x).Peaked X M x
  waits : D.QuietBeyond (R \ V)
  affordable : ∀ M a f c, Thin X M a f c → ∀ x, (D x).Fund (cost X M a f) (2*c)
  equality : ∀ M a f c, Thin X M a f c → ∀ u : I → ℂ, (∀ i, ‖u i‖ ≤ f i) →
      BulkGas.Z X R u = Complex.exp (D.plays u) * BulkGas.Z X V u

open BulkGas (Z)

private lemma skip (X : I → Support n) (R : Support n) : Peeling X R R (fun _ => blank) := by
  constructor
  · rintro _ _ ⟨⟩
  · intro x _; exact (inferInstance : IsEmpty Empty)
  · intro _ _ _ c h _; exact Absolute.loosen (Absolute.empty _) (mul_nonneg (by norm_num) h.sane)
  intro _ _ _ _ _ u _; simp [Chorus.plays,blank,lineSum]

private lemma singles [Countable I] (X : I → Support n) (hn : ∀ i, (X i).Nonempty) (R : Support n) (x : Site n)
    (H : ∀ s ⊆ R.erase x, ∃ D, Peeling X (R.erase x) s D) : ∃ T : Text I,
    (∀ M, T.Peaked X M x) ∧ (∀ M a f c, Thin X M a f c → T.Fund (cost X M a f) (2*c)) ∧
    ∀ M a f c, Thin X M a f c → ∀ u : I → ℂ, (∀ i, ‖u i‖ ≤ f i) →
      Z X R u = Complex.exp (T.lineSum u) * Z X (R.erase x) u := by
  let J := BulkGas.Face X R x
  let L (i : J) := X i.val
  have he i : R \ L i ⊆ R.erase x := by
    intro j hj; obtain ⟨hj,hj'⟩ := mem_sdiff.mp hj
    have ht := i.property.1
    exact mem_erase.mpr ⟨fun hh => hj' (hh ▸ ht),hj⟩
  choose D hD using fun i => H (R \ L i) (he i)
  let A (i) := ((D i).tune.scale (-1))
  let E (i : J) := (atom i.val).pair (A i).expanding
  let S : Text I := Text.bind E
  have hW i : (D i).QuietBeyond (L i) := by
    intro j hh; apply (hD i).waits; intro h
    obtain ⟨h,hj⟩ := mem_sdiff.mp h; exact hj (mem_sdiff.mpr ⟨mem_of_mem_erase h,hh⟩)
  have hG M a f c (hh : Thin X M a f c) i := Chorus.finances _ (L i) (hW i)
    (mul_nonneg (by norm_num) hh.sane) ((hD i).affordable M a f c hh)
  have hJ M a f c (hh : Thin X M a f c) i : (A i).Fund (cost X M a f) ((L i).card*(2*c)) := by
    simpa only [A,norm_neg,norm_one,one_mul] using Text.scale_fund _ (-1) (hG M a f c hh i)
  have hA M a f c (hh : Thin X M a f c) : S.Fund (cost X M a f) c := Text.bind_fund _ (hh.face_pay x R)
    fun i => Text.pair_fund _ _ (Text.atom_fund i.val (fun k => (hh.val k).trans (hh.enlarges _))) <|
        Text.expanding_fund _ (hJ M a f c hh i)
  refine ⟨S.pressed,fun M => ?_, fun M a f c hh => Text.press_fund S (hA M a f c hh) hh.cap,?_⟩
  · have hi (i : J) : (E i).Peaked X M x := Text.atom_adjoined i.property.1
      ((((D i).sticky (L i) (hW i) ((hD i).roots M)).scale (-1)).expanding)
    exact (show S.Peaked X M x from fun i => hi i.1 i.2).pressed
  intro M a f c hh u hu
  have hv i : ‖u i‖ ≤ cost X M a f i := (hu i).trans (hh.enlarges i)
  have hb (i : J) : (E i).lineSum u = u i.val * Complex.exp (- (D i).plays u) := by
    unfold E
    rw [Text.pair_sum _ _ (Text.atom_fund i.val (f:=cost X M a f) fun k => (norm_nonneg _).trans (hv k))
      (Text.expanding_fund _ (hJ M a f c hh i)) hv, Text.atom_sum,Text.expanding_sum _ (hJ M a f c hh i) hv]
    simp [A,Text.scale_sum,(D i).tunes (hG _ _ _ _ hh i) hv]
  have hf := Absolute.account hn hh.hit (add_nonneg hh.ok zero_le_one)
  have hs := hf.of_nonneg_of_le (fun i => norm_nonneg (u i)) hu
  rw [press_sum _ (hA M a f c hh) hh.cap hv, Text.bind_sum E (hA M a f c hh) hv,
    BulkGas.delete X R x hs, add_mul, one_mul,← tsum_mul_right]
  congr 1
  refine tsum_congr fun i => ?_
  rw [hb,(hD i).equality M a f c hh u hu,mul_assoc (u i.val),← mul_assoc (Complex.exp _),← Complex.exp_add]
  simp [L]

private lemma shorter [Countable I] (X : I → Support n) (hn : ∀ i, (X i).Nonempty) (R : Support n) :
    ∀ V ⊆ R, ∃ D, Peeling X R V D := by
  induction R using Finset.strongInduction with
  | H R ih =>
    intro V hV
    by_cases e : R = V
    · subst V; exact ⟨_,skip X R⟩
    have he : ¬ R ⊆ V := fun h => e (Subset.antisymm h hV)
    obtain ⟨x,hx,hk⟩ := Finset.not_subset.mp he
    have hh := ih (R.erase x) (erase_ssubset hx)
    obtain ⟨T,hT,ha,hZ⟩ := singles X hn R x hh
    obtain ⟨A,hA⟩ := hh V fun i hi => mem_erase.mpr ⟨fun he => hk (he ▸ hi),hV hi⟩
    have hK : IsEmpty (A x).address := hA.waits _ (by simp)
    let D (j : Site n) := if j = x then T else A j
    refine ⟨D, ⟨?_,?_,?_,?_⟩⟩
    · intro M y; unfold D; split
      · rename_i hj; rw [hj]; exact hT _
      exact hA.roots _ _
    · intro y hy
      unfold D; split
      · rename_i h; exact False.elim (hy (h ▸ mem_sdiff.mpr ⟨hx,hk⟩))
      apply hA.waits; exact fun H => hy (sdiff_subset_sdiff (erase_subset ..) le_rfl H)
    · intro M a f c h y; unfold D; split
      · exact ha _ _ _ _ h
      exact hA.affordable _ _ _ _ h _
    intro M a f c h u hu
    have hp : Chorus.plays D u = T.lineSum u + A.plays u := by
      unfold Chorus.plays
      rw [← add_sum_erase _ _ (mem_univ x), show D x=T from if_pos rfl]
      congr 1
      rw [← add_sum_erase _ _ (mem_univ x),show (A x).lineSum u=0 from tsum_empty,zero_add]
      apply Finset.sum_congr rfl; intro j hj; unfold D; rw [if_neg (mem_erase.mp hj).1]
    rw [hp, Complex.exp_add, hZ M a f c h u hu,hA.equality M a f c h u hu,mul_assoc]

/-- Cluster ledger valid with rates uniform on all finite 4-tori and on countable addresses,
even with terms on wrapping supports. Uses only thin input site-hit norm. -/
theorem peel [Countable I] (X : I → Support n) (hn : ∀ i, (X i).Nonempty)
    (R V : Support n) (hV : V ⊆ R) : ∃ D, Peeling X R V D := shorter X hn R V hV
end YM.Multi.Vacuum.Cluster
