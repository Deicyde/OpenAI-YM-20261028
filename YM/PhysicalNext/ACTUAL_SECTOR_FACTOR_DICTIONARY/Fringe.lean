import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Order



/-!
# A normalization *without* using any K value

At a marked K address the old physical amplitude may be zero. So
`Spot.canvas`, `schedule.exhaust` etc might hold simply by old K=0 and
are not enough. Check the gate/log edits also on these stripped Products.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Formal
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Check Parcel   SectorNext.Reconnect
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S) (h : Lit D)
    (F : Forest S.ratio) (A : Stores S) (k₀ k : S.Choices) (V : Config G c) (b : Finset ℕ)
local notation "x"=>D.betaHat
local notation "B"=>radiusB x
local notation "H₀"=>chosen D F k₀ A k
local notation "T"=>Voice.Check.Test

-- Exactly the non-K gates of H₀.
abbrev Quizzes (u : Spot D) := u.TestIndex ⊕ Lattice.Site f

def original (u : Spot D) : Quizzes D u→u.Gates b := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
lemma orig_inj (u : Spot D) : Injective (original D b u) := by
  rintro (i|i) (j|j) e <;> simpa [original] using e

-- Extract the independent nonK address, even at inactive and padded.
def translation (u : Spot D) : Quizzes D u → T c f := Sum.elim
    (Sum.elim Test.fine (Sum.elim Test.noise (Sum.elim Test.frame (Sum.elim Test.predictor (fun i=>Test.screen i.val.val))))) Test.void
lemma translations (u : Spot D) (i : Quizzes D u) : Sum.inl (translation D u i) = historical D u (original D b u i) := by
  rcases i with (i|i|i|i|i)|i <;> rfl
lemma phrases_inj (u : Spot D) : Injective (translation D u) := by
  intro i j e
  apply orig_inj D ∅ u; apply admits D u (b:=∅)
  rw [←translations,←translations,e]
lemma phrases (u : Spot D) (i : T c f) : i ∈ Set.range (translation D u) ↔ live x u.F u.A b (.inl i) := by
  rw [← controlled D u b (.inl i)]
  constructor
  · rintro ⟨j,rfl⟩; exact ⟨original D b u j,(translations ..).symm⟩
  rintro ⟨j,hj⟩
  rcases j with j|j|j
  · exact ⟨.inl j,Sum.inl_injective (((translations D b u (.inl j))).trans hj)⟩
  · exact False.elim (by cases hj)
  exact ⟨.inr j,Sum.inl_injective (((translations D b u (.inr j))).trans hj)⟩



def exam (uPAGE : (H₀).Visual) (j : Quizzes D (H₀)) : ℝ := (H₀).gate b (original D b H₀ j) V uPAGE

-- Don't use Charts off domain; every equality invoked against real bills.
include h
lemma answers (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (i : Quizzes D (H₀)) : films D (translation D H₀ i) F A b k V (Print.backdrop x A F uPAGE) = exam D F A k₀ k V b uPAGE i := by
  have ha := true_gate D h.toApp F A k k₀ V b hc.flags (Print.backdrop x A F uPAGE) (original D b H₀ i)
  dsimp only at ha
  rw [Print.rollback,←translations] at ha
  exact ha.symm

lemma coat_cost (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (ok : (∏ i : Quizzes D (H₀), exam D F A k₀ k V b uPAGE i) ≠0) (s : Support c) :
    tarp D s F A b k V (Print.backdrop x A F uPAGE)=1 := by
  apply Spotter.protects D h.toApp F k₀ A k b V hc
  rw [Print.rollback]
  intro i
  exact (Finset.prod_ne_zero_iff.mp ok) _ (Finset.mem_univ (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))) : Quizzes D (H₀)))

-- Here we deliberately recheck `Parcel.diets` under ONLY the fine gates.
private lemma budget_cost (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (s : Signed) (j : Spot.Shape c f)
    (hn : ¬wants D A (.row (s,j))) (ok : (∏ i : Quizzes D (H₀),exam D F A k₀ k V b uPAGE i) ≠ 0) :
    Defenses.diet D (s.act (hinge S j)) F A b k V (Print.backdrop x A F uPAGE)=1 := by
  let o:= s.act (hinge S j)
  unfold Defenses.diet; refine Finset.prod_eq_one fun i hi=>?_
  have ht : separation o (S.ratio.parent i.1) ≤ 6*B := (Finset.mem_filter.mp hi).2
  have hx : i∉A.costs := by
    intro hz; apply hn; apply (records ..).mpr
    have h0:=Finset.mem_image_of_mem S.ratio.parent (Work.E01.base_touched i)
    refine ⟨o,Finset.mem_singleton_self _, S.ratio.parent i.1, Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i,hz,h0⟩)),?_⟩
    rw [separation_comm]; change separation o _ ≤ 200*B; omega
  let t : Quizzes D (H₀) := .inl (.inl i)
  have hv := Finset.prod_ne_zero_iff.mp ok t (Finset.mem_univ _)
  rw [←answers D h F A k₀ k V b uPAGE hc] at hv
  let U:=skin D F A b k V (Print.backdrop x A F uPAGE); let d:=fiery G D.betaHat S.patch.L
  have hD := D.paidScale
  change fineBit (chosen D F k A k) i U ≠0 at hv
  unfold fineBit at hv; dsimp only at hv; rw [if_neg (show i∉(chosen D F k A k).A.costs from hx)] at hv
  apply D.profile.to_one
  have hr := D.profile.chosen_lt (toll U i) (d/4) (by unfold d; positivity) hv
  have hb : 0 ≤ toll U i := G.chord_nonneg _
  have hf : toll U i/(d/2) ≤ 1 := (div_le_one (by unfold d; positivity)).mpr (by linarith)
  have hp : 0 ≤ toll U i/(d/2) := by unfold d; positivity
  change (toll U i/(d/2))^2 ≤ 1
  nlinarith

lemma arranged (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (ok : (∏ i : Quizzes D (H₀),exam D F A k₀ k V b uPAGE i) ≠0) (j : (H₀).Log) :
    Parcel.receipt D (written D H₀ j) F A b k V (Print.backdrop x A F uPAGE) = (H₀).price (packets D F k₀ A k h) j V uPAGE := by
  have hX := cream D h F A k k₀ V b hc.flags (Print.backdrop x A F uPAGE) j
  dsimp only at hX
  rw [Print.rollback] at hX
  rw [hX]; unfold Parcel.receipt; split
  · rfl
  rename_i ht
  generalize he : written D H₀ j=i at *
  unfold Defenses.introduce
  have hp : Defenses.barrier D i F A b k V (Print.backdrop x A F uPAGE)=1 := by
    unfold Defenses.barrier; split; exact coat_cost D h F A k₀ k V b uPAGE hc ok _; rfl
  have hb : Defenses.budget D i F A b k V (Print.backdrop x A F uPAGE)=1 := by
    cases i with
    | row j=> simp only [ Defenses.budget]; split; exact budget_cost D h F A k₀ k V b uPAGE hc j.1 j.2 ht ok; rfl
    | _=>rfl
  rw [hp,hb,mul_one,mul_one]

def poster (uPAGE : (H₀).Visual) (i : T c f) : ℝ := if live x F A b (Sum.inl i) then Parcel.frontage D i F A b k V (Print.backdrop x A F uPAGE) else 1

-- `schedule.first` chronology, reused here on these quizzes.
lemma prices (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (hn : D.Nonoverlap b) (i : Quizzes D H₀) (ht : ∀ j : Quizzes D H₀,
    timing (.inl (translation D H₀ j)) < timing (Sum.inl (translation D H₀ i)) → exam D F A k₀ k V b uPAGE j ≠ 0) :
    poster D F A k₀ k V b uPAGE (translation D H₀ i) = exam D F A k₀ k V b uPAGE i := by
  unfold poster
  rw [if_pos (show live D.betaHat F A b (.inl (translation D H₀ i)) from (phrases D b H₀ _).mp ⟨i,rfl⟩)]
  let u:=original D b H₀ i; let L:=schedule D k₀ b h F A k 0 hn
  apply Eq.trans (show Parcel.frontage D (translation D (H₀) i) F A b k V (Print.backdrop x A F uPAGE)=L.stored u V uPAGE from ?_) (L.first _ _ _ hc ?_)
  · change _= (historical D H₀ u).elim (frontage D) (intact D) F A b k V (Print.backdrop x A F uPAGE); rw [← translations]; rfl
  rintro (j|j|j)
  · have hg := ht (.inl j); rw [translations D b,translations D b] at hg; exact hg
  · have he : L.layer u≤1 := by
      change timing (historical D H₀ u) ≤1
      cases historical D H₀ u with
      | inr => exact Nat.le_refl 1
      | inl i=>cases i <;> simp [timing]
    exact fun he1=>False.elim (he.not_gt he1) -- layer inr K rfl
  · have hg := ht (.inr j); rw [translations D b,translations D b] at hg; exact hg

-- all irrelevant Test names padded by one. Compare through injection.
-- export Fintype for subsequent Consumers.
scoped instance testing : Fintype (T c f) := Fintype.ofFinite _
lemma feed (uPAGE : (H₀).Visual) (hc : (H₀).Clearing V) (hi : D.Nonoverlap b) :
    ∏ i,poster D F A k₀ k V b uPAGE i = ∏ i,exam D F A k₀ k V b uPAGE i := by
  let t:=translation D H₀
  let q (i : Quizzes D H₀) := timing (Sum.inl (t i))
  let p:=exam D F A k₀ k V b uPAGE
  let r:=poster D F A k₀ k V b uPAGE
  change ∏ i,r i = ∏ i,p i
  rw [← Finset.prod_subset (f:=r) (Finset.subset_univ ((Finset.univ : Finset (Quizzes D H₀)).image t)) ?_,
    Finset.prod_image (phrases_inj D H₀).injOn]
  swap
  · intro i _ he; apply if_neg
    intro hv; obtain ⟨j,hj⟩:=(phrases D b H₀ i).2 hv
    exact he (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩)
  by_cases he : ∀ i,p i≠0
  · exact Finset.prod_congr rfl fun i _=> prices D h F A k₀ k V b uPAGE hc hi i (fun j _=>he j)
  push Not at he
  let s:=Finset.univ.filter fun i=>p i=0
  obtain ⟨i,hj⟩:=he
  obtain ⟨j,h₁,h₂⟩:=Finset.exists_min_image s q (⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
  have hp : p j=0 := (Finset.mem_filter.mp h₁).2
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hp]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Eq.trans (prices D h F A k₀ k V b uPAGE hc hi j ?_) hp
  intro u hu hz; exact hu.not_ge (h₂ u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩))
end YM.PhysicalNext.Dictionary.Formal
