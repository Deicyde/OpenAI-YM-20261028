import YM.MultiNext.VACUUM_STABILITY.FirstGas

set_option warningAsError false

/-!
# Local post-log move, single actual term

Implements e.g.  on canonical singleton. Section operand arbitrary (later
readout). This time pays the union and BOTH W families and a genuine attaching factor for
every amplitude at which incoming term is priced.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Tune
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {P : BudgetPoint}

/-- Change support of a canonical linear term with a recorded author and a paid price.
The anchor at which to pay may differ from the one the deletion happened to use. -/
structure Exchange (F : SmoothLetter V G n) where
  placement : Site n
  contained : placement ∈ F.zone
  ringSites : Support n
  boss : placement ∈ ringSites
  portrait : Config G n → ℂ
  fiat : ℂ

namespace Exchange
variable {F : SmoothLetter V G n} (D : Exchange F)

def jointly := F.zone ∪ D.ringSites

def left : SmoothLetter V G n := ⟨D.jointly, ⟨F.stamp.name,F.stamp.ink-D.portrait⟩,D.placement,mem_union_left _ D.contained⟩
def right : SmoothLetter V G n := ⟨D.ringSites,⟨F.stamp.name,D.portrait-(fun _ => D.fiat)⟩,D.placement,D.boss⟩

def tag (P : BudgetPoint) : HardLetter V G n :=
  { zone := D.jointly, kept := ⟨_, D.left.origin⟩
    stamp := ⟨F.stamp.name, masked P.threshold F.zone F.stamp.ink -
      (masked P.threshold D.left.zone D.left.stamp.ink +
       masked P.threshold D.right.zone D.right.stamp.ink + fun _ => D.fiat)⟩ }



lemma needy (P : BudgetPoint) (U : Config G n) (hu : Healthy P.threshold D.jointly U) : (D.tag P).stamp.ink U = 0 := by
  have hx : Healthy P.threshold F.zone U := Finset.disjoint_of_subset_left Finset.subset_union_left hu
  have hy : Healthy P.threshold D.ringSites U := Finset.disjoint_of_subset_left Finset.subset_union_right hu
  simp [tag,left,right,hu,hx,hy]

structure Receipted (P : BudgetPoint) (m : ℕ) (χ : ℝ) : Prop where
  enough : 1 ≤ m
  spans : coverNumber P.B D.ringSites ≤ m
  safe : 1 ≤ χ
  usable : P.Regular D.ringSites D.portrait
  -- universal linear bound, so independent of word budget at each z.
  currency c : P.supBounds D.placement F.zone F.stamp.ink c →
    P.supBounds D.placement D.ringSites D.portrait (χ*c) ∧ ‖D.fiat‖ ≤ χ*c

lemma span_sum {m} {χ} (h : D.Receipted P m χ) : coverNumber P.B D.jointly ≤ coverNumber P.B F.zone+m := by
  apply (Corona.meets_sum D.contained D.boss P.B).trans; gcongr; exact h.spans

private lemma reg_const (Y : Support n) (c : ℂ) : P.Regular Y (fun _ : Config G n => c) := by
  have hs := path_scaled c (regular_unit (G:=G) P Y)
  have he : (fun _ : Config G n => c) = c • (1: Config G n → ℂ) := by ext1 i; simp
  exact he ▸ hs

private lemma span_op (Y : Support n) {f g : Config G n → ℂ} (h : Spanned P Y f) (h' : Spanned P Y g) :
    Spanned P Y (f+g) ∧ Spanned P Y (f-g) := by
  exact ⟨⟨h.meas.add h'.meas, fun i U => by simp only [Pi.add_apply,h.gauge i U,h'.gauge i U],fun U V hx he =>
      congrArg₂ (· + ·) (h.reads U V hx he) (h'.reads U V hx he)⟩,
    ⟨h.meas.sub h'.meas, fun i U => by simp only [Pi.sub_apply,h.gauge i U,h'.gauge i U],fun U V hx he =>
      congrArg₂ (· - ·) (h.reads U V hx he) (h'.reads U V hx he)⟩⟩

lemma converted (hF : P.Regular F.zone F.stamp.ink) {m χ} (h : D.Receipted P m χ) :
    P.Regular D.left.zone D.left.stamp.ink ∧ P.Regular D.right.zone D.right.stamp.ink ∧
      Spanned P (D.tag P).zone (D.tag P).stamp.ink := by
  have ht := regular_sub (regular_larger hF (s:=F.zone) (u:=D.jointly) Finset.subset_union_left)
    (regular_larger h.usable (u:=D.jointly) Finset.subset_union_right)
  have hh := regular_sub h.usable (reg_const D.ringSites D.fiat)
  refine ⟨ht,hh,?_⟩
  have he := (Spanned.regular hF).larger D.jointly Finset.subset_union_left
  have hf := (Spanned.regular hh).larger D.jointly Finset.subset_union_right
  have hg : Spanned P D.jointly (fun _ : Config G n => D.fiat) := ⟨measurable_const,fun _ _ => rfl,fun _ _ _ _ => rfl⟩
  exact (span_op _ he (span_op _ (span_op _ (Spanned.regular ht) hf).1 hg).1).2

lemma scaled {m χ} (h : D.Receipted P m χ) (z : ℂ) {f : ℝ} (he : P.supBounds D.placement F.zone (z • F.stamp.ink) f) :
    P.supBounds D.placement D.ringSites (z • D.portrait) (χ*f) ∧ ‖z * D.fiat‖ ≤ χ*f := by
  by_cases ht : z=0
  · subst z
    rw [zero_smul,zero_mul,norm_zero]; have hx : 0≤χ*f:=mul_nonneg (zero_le_one.trans h.safe) he.1
    refine ⟨⟨hx,fun U hu l hl hh => ((null_path P _).2 _).2 U hu l hl hh |>.trans hx⟩,hx⟩
  have hf := bound_smul z⁻¹ he
  rw [inv_smul_smul₀ ht] at hf
  obtain ⟨ha,hb⟩:=h.currency _ hf
  have hv : ‖z‖*(χ*(‖z⁻¹‖*f))=χ*f := by rw [norm_inv]; field_simp
  exact ⟨hv ▸ bound_smul z ha,(norm_mul ..).trans_le ((mul_le_mul_of_nonneg_left hb (norm_nonneg z)).trans_eq hv)⟩

private lemma resize {Y : Support n} {x : Config G n → ℂ} {p q : ℝ} (o : Site n) (h : P.supBounds o Y x p)
    (he : p ≤ q) : P.supBounds o Y x q :=
  ⟨h.1.trans he,fun U hu l hl hb => (h.2 U hu l hl hb).trans he⟩

/-- Uniform direction shifts cost even away from the fill's primary root. -/
private lemma enlarge {Y : Support n} {o o' : Site n} {x : Config G n → ℂ} (N : ℕ) (hi : 0 < N)
    (he : separation o o' ≤ N * Hits.stride P.B) (hx : P.Regular Y x) {c : ℝ} (h : P.supBounds o Y x c) :
    P.supBounds o' Y x (c*(rate P N)^P.order) := by
  have hs : 1 ≤ rate P N := rate_hi ..
  refine ⟨mul_nonneg h.1 (pow_nonneg (zero_le_one.trans hs) _),fun U hu l hl hL => ?_⟩
  have hv := crossing hu hx h (show (separation o o':ℝ) ≤ (N*Hits.stride P.B:ℕ) by exact_mod_cast he)
  apply (hv.caps l hl hL).trans
  apply mul_le_mul_of_nonneg_left _ h.1
  have hb : (1+((N*Hits.stride P.B:ℕ):ℝ)) ^ P.power ≤ rate P N := by
    simpa only [Nat.cast_one,one_mul] using
      rate_price P N 1 hi
  exact (pow_le_pow_left₀ hv.sane hb _).trans (pow_le_pow_right₀ hs hl)

private lemma mask_cost {u : Config G n → ℂ} {Y : Support n} {c : ℝ} {o : Site n} (z : ℂ)
    (h : P.supBounds o Y (z • u) c) (U : Config G n) : ‖z*masked P.threshold Y u U‖ ≤ c := by
  by_cases H : Healthy P.threshold Y U
  · rw [masked_eq _ _ _ _ H]; exact h.2 U H [] (by simp) (by simp)
  simp only [masked_ne _ _ _ _ H,mul_zero,norm_zero]; exact h.1

lemma issued (hF : P.Regular F.zone F.stamp.ink) {m χ} (h : D.Receipted P m χ) (z : ℂ) {f : ℝ}
    (hf : P.supBounds D.placement F.zone (z • F.stamp.ink) f) :
    let a := (rate P (coverNumber P.B F.zone + m))^P.order
    (∀ x∈D.left.zone, P.supBounds x D.left.zone (z • D.left.stamp.ink) ((2*χ)*f*a)) ∧
      (∀ x∈D.right.zone,P.supBounds x D.right.zone (z • D.right.stamp.ink) ((2*χ)*f*a)) ∧
      ∀ U, ‖z * (D.tag P).stamp.ink U‖ ≤ (6*χ)*f*a := by
  intro a; obtain ⟨he,hz⟩:=D.scaled h z hf
  let t := coverNumber P.B F.zone+m
  have hs : coverNumber P.B D.jointly ≤ t := span_sum D h
  have hQ x (hx : x∈D.jointly) : separation D.placement x ≤ t*Hits.stride P.B :=
    (Hits.distance D.jointly P.B D.left.origin hx).trans (Nat.mul_le_mul_right _ hs)
  have hl : 0<t := (Hits.cover_pos _ _ ⟨D.placement,D.left.origin⟩).trans_le hs
  have hP := h.safe; have hW := hf.1
  have ht : P.supBounds D.placement D.left.zone (z • D.left.stamp.ink) ((2*χ)*f) := by
    dsimp only [left]; rw [smul_sub]
    apply resize _ (bound_sub (regular_larger (path_scaled z hF) (u:=D.jointly) Finset.subset_union_left)
      (regular_larger (path_scaled z h.usable) Finset.subset_union_right) (bound_larger hf Finset.subset_union_left) (bound_larger he Finset.subset_union_right))
    nlinarith
  have hj : P.supBounds D.placement D.right.zone (z • D.right.stamp.ink) ((2*χ)*f) := by
    dsimp only [right]; rw [smul_sub]
    apply resize _ (bound_sub (path_scaled z h.usable) (path_scaled z (reg_const _ D.fiat)) he
      (b:=χ*f) ?_)
    · nlinarith
    refine ⟨mul_nonneg (zero_le_one.trans h.safe) hW, fun U hu l hl hb => ?_⟩
    have he' : z • (fun _ : Config G n => D.fiat) = (fun _ => z*D.fiat) := rfl
    rw [he',Work.G07.left_const]; split
    · exact hz
    exact norm_zero.le.trans (mul_nonneg (zero_le_one.trans h.safe) hW)
  have hv := D.converted hF h
  refine ⟨fun x hx => enlarge _ hl (hQ _ hx) (path_scaled z hv.1) ht,
    fun x hx => enlarge _ hl (hQ _ (mem_union_right _ hx)) (path_scaled z hv.2.1) hj,?_⟩
  intro U; have hl' := mask_cost z ht U; have hr := mask_cost z hj U; have hu := mask_cost z hf U
  change ‖z * (masked P.threshold F.zone _ U - ((_ + _) + _))‖ ≤ _
  rw [mul_sub,mul_add,mul_add]
  refine ((norm_sub_le ..).trans (add_le_add hu ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans
    (add_le_add hl' hr)) hz)))).trans ?_
  have hh : 1 ≤ a := one_le_pow₀ (rate_hi ..)
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h.safe) hf.1) (sub_nonneg.mpr hh),
    mul_nonneg hW (sub_nonneg.mpr hh)]
end Exchange
end YM.Multi.Vacuum.Tune
