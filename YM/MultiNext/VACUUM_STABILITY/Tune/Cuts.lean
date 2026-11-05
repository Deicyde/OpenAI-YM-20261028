import YM.MultiNext.VACUUM_STABILITY.Chapters
import YM.MultiNext.VACUUM_STABILITY.Deploy
import YM.MultiNext.VACUUM_STABILITY.Tune.Local

set_option warningAsError false

/-!
# Choose all post-log singleton exchanges locally

One series of letters at the true deletion. Unmarked reclosure attachment identities remain a
producer input in this construction. Not assuming new choices on each z; keep all move histories
including winding labels and projected ancestry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Tune
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V : Type} {n : Side} {G : Gauge} {B : Brush V G n} {P : BudgetPoint}

/-- Base stickers all carry grade 0. Slices chosen on all addresses (including those
that will be unused). -/
structure Slicer (B : Brush V G n) where
  cuts (i : B.Line) : Exchange (B.chapter i)
  base : ℕ → HardLetter V G n

namespace Slicer
variable (S : Slicer B)

-- every unused pitch records zero. Don't change the support on an evaluated term

def quiet (F : SmoothLetter V G n) : SmoothLetter V G n := { F with stamp := ⟨0,0⟩ }
def eraseChime (F : HardLetter V G n) : HardLetter V G n := { F with stamp := ⟨0,0⟩ }

def partL (T : Finset V) (i : B.Line) : SmoothLetter V G n :=
    if along T (B.chapter i).stamp.name then (S.cuts i).left else quiet (S.cuts i).left

def partR (T : Finset V) (i : B.Line) : SmoothLetter V G n :=
    if along T (B.chapter i).stamp.name then (S.cuts i).right else quiet (S.cuts i).right

def flagTerm (T : Finset V) (P : BudgetPoint) (i : B.Line) : HardLetter V G n :=
    if along T (B.chapter i).stamp.name then (S.cuts i).tag P else eraseChime ((S.cuts i).tag P)

def brine (T : Finset V) := Sum.elim (S.partL T) (S.partR T)

def jointList (T : Finset V) (P : BudgetPoint) := Sum.elim (S.flagTerm T P) S.base

-- fixed pads even on empty lines

def tent (V : Type) (G : Gauge) (n : Side) : SmoothLetter V G n := ⟨{0}, ⟨0,0⟩,0,by simp⟩

def stub (V : Type) (G : Gauge) (n : Side) : HardLetter V G n := ⟨{0},⟨0,0⟩, by simp⟩

def tribute (x : V) := ∑' i : B.Line, if (B.chapter i).stamp.name = spike x then
    (S.cuts i).fiat else 0

def package (P : BudgetPoint) (T : Finset V) : Restock V G n :=
  { wrap := Pad.wide (S.brine T) (tent V G n)
    sticker := Pad.wide (S.jointList T P) (stub V G n)
    outgoing := fun x => if x∈T then B.pay x+S.tribute x else 0 }

/-- Local inputs: o anchors of the cut should honor any used reference axes
    (e.g. `Cuts.cuts i` if the i-th log word is on some reference axis is
    its exchange at that anchor; the readout decision independent of z).
    No projection work needed on higher markers, only on `T` axes. -/
structure Ticket (P : BudgetPoint) (L : V → Support n → Prop) (T : Finset V) (m : ℕ) (χ : ℝ) : Prop where
  -- initial
  lawful i : P.Regular (B.u i).zone (B.u i).stamp.ink
  begun i x : x ∈ (B.u i).stamp.name.support → L x (B.u i).zone
  legible i : Legible P (B.pack i) (B.d i).ink
  sits i x : x∈ (B.d i).name.support → L x (B.pack i).zone
  cover i : i∉T → B.pay i=0
  -- base after-vacuum corrections, agree with P when assembled separately
  ins i : Spanned P (S.base i).zone (S.base i).stamp.ink
  baseFlag i U : Healthy P.threshold (S.base i).zone U → (S.base i).stamp.ink U=0
  zero i : (S.base i).stamp.name = 0
  -- per-log line "exchange", with constants pre-purchased for p or stage stronger
  expenditure i : (S.cuts i).Receipted P m χ
  feasible i x : x∈T → (B.chapter i).stamp.name=spike x → L x (S.cuts i).ringSites

lemma union_zones (T : Finset V) (i : B.Line) : (S.partL T i).zone = (S.cuts i).jointly ∧ (S.partR T i).zone = (S.cuts i).ringSites ∧
    (S.flagTerm T P i).zone=(S.cuts i).jointly := by
  by_cases he : along T (B.chapter i).stamp.name <;> simp [partL,partR,flagTerm,he,quiet,eraseChime,
    Exchange.left,Exchange.right, Exchange.tag]

private lemma working {L : V → Support n → Prop} {T : Finset V} (hv : Widens L) {m χ} (h : S.Ticket P L T m χ) (i) :
    P.Regular (S.partL T i).zone (S.partL T i).stamp.ink ∧
      P.Regular (S.partR T i).zone (S.partR T i).stamp.ink ∧
      Spanned P (S.flagTerm T P i).zone (S.flagTerm T P i).stamp.ink ∧
      ∀ x, (x∈(S.partL T i).stamp.name.support → L x (S.partL T i).zone) ∧
        (x∈(S.partR T i).stamp.name.support → L x (S.partR T i).zone) ∧
        (x∈(S.flagTerm T P i).stamp.name.support → L x (S.flagTerm T P i).zone) := by
  have hf : P.Regular (B.chapter i).zone (B.chapter i).stamp.ink := Jets.stanza_regular _ _ _ h.lawful _
  unfold partL partR flagTerm; split
  · rename_i hx
    obtain ⟨he,hg,hj⟩:= (S.cuts i).converted hf (h.expenditure i)
    refine ⟨he,hg,hj,?_⟩
    obtain ⟨v,hx,hK⟩:=hx
    have he := h.feasible i v hx hK
    intro x
    have h : x∈(B.chapter i).stamp.name.support → L x (S.cuts i).ringSites := by
      intro hv; rw [hK] at hv; have hh : x=v := by simpa [spike] using hv
      exact hh ▸ he
    have hf : x∈(B.chapter i).stamp.name.support → L x (S.cuts i).jointly := fun hh =>
      hv x _ _ Finset.subset_union_right (h hh)
    exact ⟨hf,h,hf⟩
  simp only [quiet,eraseChime,Finsupp.support_zero,Finset.notMem_empty,false_imp_iff,and_self,implies_true,and_true]
  exact ⟨(null_path P _).1,(null_path P _).1,
    ⟨measurable_const,fun _ _ => rfl, fun _ _ _ _ => rfl⟩⟩

private def fitted (P : BudgetPoint) (L : V → Support n → Prop) (T : Finset V) (F : SmoothLetter V G n) :=
    P.Regular F.zone F.stamp.ink ∧ (along T F.stamp.name ∨ (F.stamp.name=0 ∧ F.stamp.ink=0)) ∧
       (∀ x, x∈F.stamp.name.support → L x F.zone)
private def fitHard (P : BudgetPoint) (L : V → Support n → Prop) (T : Finset V) (F : HardLetter V G n) :=
    Spanned P F.zone F.stamp.ink ∧ (along T F.stamp.name ∨ F.stamp.name=0) ∧
      (∀ U, F.stamp.ink U≠0 → ¬Healthy P.threshold F.zone U) ∧ ∀ x, x∈F.stamp.name.support → L x F.zone

lemma gathered {L : V → Support n → Prop} {T : Finset V} {m χ} (h : S.Ticket P L T m χ) (hh : Widens L) :
    Supported B (S.package P T) P L T := by
  have hs i := S.working hh h i
  have hw (i : ℕ) : fitted P L T ((S.package P T).wrap i) := by
    refine Pad.all _ _ (fitted P L T) _ ?_ ?_
    · rintro (i|i)
      · obtain ⟨ht,-,-,hb⟩:=hs i; refine ⟨ht,?_,fun x => (hb x).1⟩
        dsimp only [brine,Sum.elim_inl]
        unfold partL; split
        · rename_i hx; exact Or.inl (show along _ _ from hx)
        exact Or.inr ⟨rfl,rfl⟩
      obtain ⟨-,he,-,hb⟩:=hs i; refine ⟨he,?_,fun x => (hb x).2.1⟩
      dsimp only [brine,Sum.elim_inr]
      unfold partR; split
      · rename_i hx; exact Or.inl (show along _ _ from hx)
      exact Or.inr ⟨rfl,rfl⟩
    exact ⟨(null_path P _).1, Or.inr ⟨rfl,rfl⟩,fun x => by simp [tent]⟩
  have ht (i : ℕ) : fitHard P L T ((S.package P T).sticker i) := by
    refine Pad.all _ _ (fitHard P L T) _ ?_ ?_
    · rintro (i|i)
      · change fitHard _ _ _ (S.flagTerm T P i); obtain ⟨-,-,hs,hx⟩:=hs i
        refine ⟨hs, ?_, ?_, fun x => (hx x).2.2⟩
        · unfold flagTerm; split
          · rename_i hx; exact Or.inl (show along _ _ from hx)
          exact Or.inr rfl
        unfold flagTerm; split
        · exact fun U h he => h ((S.cuts i).needy P U he)
        exact fun U h _ => h rfl
      refine ⟨h.ins _, Or.inr (h.zero i),fun U he hx => he (h.baseFlag _ _ hx), fun x => ?_⟩
      change x∈(S.base _).stamp.name.support → _
      rw [h.zero i]; simp
    exact ⟨⟨measurable_const,fun _ _ => rfl,fun _ _ _ _=>rfl⟩, Or.inr rfl,fun _ ht _ => ht rfl,
      fun _ => by simp [stub]⟩
  exact ⟨h.lawful,h.legible, fun i => (hw i).1,fun i => (ht i).1,fun i => (ht i).2.2.1,h.begun,h.sits,
    fun i => (hw i).2.2,fun i => (ht i).2.2.2,fun i hh => ⟨h.cover i hh,if_neg hh⟩,fun i => (hw i).2.1, fun i => (ht i).2.1⟩
end Slicer
end YM.Multi.Vacuum.Tune
