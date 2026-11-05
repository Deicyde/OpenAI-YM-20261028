import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Defenses
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Issued

/-! Programme for this exact dictionary, including chronology of
protections and actual-vs-predicted spelling at each stamp.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Parcel
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussian.Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Check Voice.Defenses
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
    {F : Forest S.ratio} {A : Stores S} {k : S.Choices}
local notation "t₀" => D.betaHat
local notation "B" => radiusB D.betaHat

/-- rollout after restoring the all-doors environment. -/
def bare : Voice.Check.Test c f → Bool
  | .screen _ => false
  | _=>true

def frontage (i : Voice.Check.Test c f) : Formula G S ℝ := fun F A b k V p=>
  let u:= films D i F A b k V p
  if wanted S t₀ A i ∨ bare i=false then u else 1+(u-1)*tarp D (post S i) F A b k V p

def intact (j : ℕ) : Formula G S ℝ := fun F A b k V p=>cargo D j F A b k V p * tarp D (custody D j) F A b k V p

def timing (i : Voice.Check.Test c f ⊕ ℕ) : ℕ := match i with
  | .inl (.screen _) => 0
  | .inl _ => 1
  | .inr _ => 1

def sales (i : Voice.Check.Test c f ⊕ ℕ) := i.elim (frontage D) (intact D)

def receipt (i : ListID S) : Formula G S ℝ := fun F A b=> if wants D A i then sew D i F A b else introduce D i F A b

variable (k₀ : S.Choices) (b : Finset ℕ) (u : Spot D)

def pushcard (i : Formula G S ℝ) (V : Config G c) (p : u.Visual) : ℝ := i u.F u.A b u.k V (Print.backdrop t₀ u.A u.F p)

abbrev stores (i : u.Gates b) := pushcard D b u (sales D (historical D u i))
abbrev topcard (i : u.Log) := pushcard D b u (receipt D (written D u i))

-- proof in the exact Camera; `u` generic only for abbreviations.
local notation "U₀" => chosen D F k₀ A k

private lemma paints (h : Route.Badge.App D) (V : Config G c) (p : (U₀).Visual) (hc : (U₀).Clearing V)
    (hn : ∀ i:(U₀).ActiveKey,(U₀).gate b (.inl (.inr (.inr (.inr (.inr i))))) V p≠0) (s : Support c) :
    pushcard D b U₀ (tarp D s) V p =1 := by
  let z:=Print.backdrop t₀ A F p
  have ht (i :(U₀).ActiveKey) := hn i
  have he : Print.see t₀ A F z=p := Print.rollback ..
  rw [← he] at ht
  exact Spotter.protects D h F k₀ A k b V hc z ht s

private lemma films_back (h : Route.Badge.App D) (V : Config G c) (p : (U₀).Visual) (hc : (U₀).Clearing V) (i : (U₀).Gates b) :
    (U₀).gate b i V p=(historical D U₀ i).elim (fun j=>films D j F A b k V (Print.backdrop t₀ A F p))
      (fun j=>cargo D j F A b k V (Print.backdrop t₀ A F p)) := by
  have ht := true_gate D h F A k k₀ V b hc.flags (Print.backdrop t₀ A F p) i
  dsimp only at ht; rwa [Print.rollback] at ht

private lemma precedence (h : Route.Badge.App D) (V : Config G c) (p : (U₀).Visual) (i : (U₀).Gates b) (hc : (U₀).Clearing V)
    (ht : ∀ j, timing (historical D U₀ j) < timing (historical D U₀ i) → (U₀).gate b j V p ≠ 0) :
    stores D b U₀ i V p=(U₀).gate b i V p := by
  have hv:=films_back D k₀ b h V p hc i; rw [hv]
  change sales D (historical D U₀ i) F A b k V (Print.backdrop ..)=_
  let L:=Print.backdrop t₀ A F p
  generalize hl : historical D U₀ i=j at *
  have he (h' : 0 < timing j) (s₁) : tarp D s₁ F A b k V L=1 := paints D k₀ b h V p hc
    (fun t=>ht (.inl (.inr (.inr (.inr (.inr t))))) h') s₁
  cases j with
  | inl j =>
    unfold sales frontage; dsimp only [Sum.elim_inl]; split
    · rfl
    next hn =>
      have h' : 0<timing (Sum.inl j) := by cases j <;> first | exact zero_lt_one | exact (hn (Or.inr rfl)).elim
      change 1 + (films D j F A b k V L-1)* tarp D (post S j) F A b k V L=films D j F A b k V L; rw [he h']; ring
  | inr j =>
    change _* tarp D (custody D j) F A b k V L=_; rw [he (show 0<timing (c:=c) (f:=f) (.inr j) from zero_lt_one)]; exact mul_one _

private lemma uncoated (h : Lit D) (V : Config G c) (p : (U₀).Visual) (i : (U₀).Log) (hc : (U₀).Clearing V) :
    pushcard D b U₀ (sew D (written D U₀ i)) V p=(U₀).price (packets D F k₀ A k h) i V p := by
  have ht := cream D h F A k k₀ V b hc.flags (Print.backdrop t₀ A F p) i
  dsimp only at ht; rw [Print.rollback] at ht; exact ht.symm

private lemma diets (h : Route.Badge.App D) (s : Signed) (j : Spot.Shape c f) (V : Config G c) (p : (U₀).Visual) (hc : (U₀).Clearing V)
    (hn : ¬wants D A (.row (s,j))) (H : ∀ i,(U₀).gate b i V p≠0) :
    pushcard D b U₀ (diet D (s.act (hinge S j))) V p=1 := by
  let o:= s.act (hinge S j)
  let t:=Print.backdrop t₀ A F p
  change diet D o F A b k V t=1
  unfold diet
  refine Finset.prod_eq_one fun i hi=>?_
  have ht : separation o (S.ratio.parent i.1) ≤ 6*B := (Finset.mem_filter.mp hi).2
  have hx : i∉A.costs := by
    intro hz; apply hn
    apply (records ..).mpr
    have h0 := Finset.mem_image_of_mem S.ratio.parent (Work.E01.base_touched i)
    refine ⟨o,Finset.mem_singleton_self _, S.ratio.parent i.1, Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_biUnion.mpr ⟨i,hz,h0⟩)),?_⟩
    rw [separation_comm]; change separation o _ ≤ 200 * B; omega
  have hv := H (.inl (.inl i))
  rw [films_back D k₀ b h V p hc (.inl (.inl i))] at hv
  let U:=skin D F A b k V t; let d:= fiery G D.betaHat S.patch.L
  have hD : 0 < d := D.paidScale
  change fineBit (chosen D F k A k) i U ≠0 at hv
  unfold fineBit at hv; dsimp only at hv; rw [if_neg (show i∉(chosen D F k A k).A.costs from hx)] at hv
  apply D.profile.to_one
  have hr := D.profile.chosen_lt (toll U i) (d/4) (by positivity) hv
  have hb : 0 ≤ toll U i := G.chord_nonneg _
  have hf : toll U i/(d/2) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hp : 0 ≤ toll U i/(d/2) := by positivity
  change (toll U i/(d/2))^2 ≤ 1
  nlinarith

private lemma bill (h : Lit D) (V : Config G c) (p : (U₀).Visual) (i : (U₀).Log) (hc : (U₀).Clearing V)
    (he : ∀ j,(U₀).gate b j V p ≠ 0) :
    topcard D b U₀ i V p=(U₀).price (packets D F k₀ A k h) i V p := by
  let j := written D U₀ i
  let l:=Print.backdrop t₀ A F p
  change receipt D j F A b k V l=_
  unfold receipt; split
  next hv=>exact uncoated D k₀ b h V p i hc
  next ht=>
    change _ * budget D j F A b k V l * barrier D j F A b k V l =_
    have hq : ∀ s, tarp D s F A b k V l = 1 := paints D k₀ b h.toApp V p hc (fun j=>he _)
    have hp : barrier D j F A b k V l=1 := by unfold barrier; split; exact hq _; rfl
    have hb : budget D j F A b k V l=1 := by
      generalize hI : j=u at *; cases u with
      | row q=> simp only [budget]; split; exact diets D k₀ b h.toApp q.1 q.2 V p hc ht he; rfl
      | _=>rfl
    rw [hp,hb,mul_one,mul_one]; exact uncoated D k₀ b h V p i hc

private lemma attached (h : Lit D) (V : Config G c) (p : (U₀).Visual) (i : (U₀).Log) (hc : (U₀).Clearing V) (hi : i∈tapped D U₀) :
    topcard D b U₀ i V p=(U₀).price (packets D F k₀ A k h) i V p := by
  let j := written D U₀ i
  rw [heated] at hi; change wants D A j at hi
  change receipt D j F A b k V (Print.backdrop ..) = _
  unfold receipt; rw [if_pos hi]
  exact uncoated D k₀ b h V p i hc

private lemma preserves (h : Lit D) (V : Config G c) (p : (U₀).Visual) (i : (U₀).Gates b)
    (hc : (U₀).Clearing V) (he : i∈kept D U₀ b) : ∃ z : ℝ,z ∈ Set.Icc 0 1 ∧ stores D b U₀ i V p=(U₀).gate b i V p * z := by
  rw [films_back D k₀ b h.toApp V p hc i]; rw [stays] at he
  let l:=Print.backdrop t₀ A F p
  unfold stores pushcard; generalize hl : historical D U₀ i=j at *; cases j <;> dsimp only [sales,Sum.elim_inl,Sum.elim_inr] at *
  · exact ⟨1,⟨zero_le_one,le_rfl⟩,(if_pos (Or.inl he)).trans (mul_one _).symm⟩
  rename_i j; exact ⟨tarp D (custody D j) F A b k V l, affordable ..,rfl⟩

-- named alternatives of the remote source and E test. Retain both at
-- every E address even if compulsory/remote negative answer or gamma
-- empty. Parent Stock.stamp remains unique.
def columns (u : Spot D) (i : u.Log) (s : ℝ) : Option (u.Submenu (fun V p => Real.exp (topcard D b u i V p)-1)) :=
    match written D u i with
    | .letter j => some {
        size := 2
        buy := fun a V p=> let t:=pushcard D b u (tip (D:=D) j s) V p
                            if a.val=0 then t else Real.exp (topcard D b u i V p)-1-t
        rebuild := fun V p hv => by simp [Fin.sum_univ_two] }
    | _=> none

-- Concrete organization for any inherited complement passing original
-- disjointness. Actual variants and raw books in place, no substitution on
-- mandatory logs at uses. Noncovered A flags stay outside.
def schedule (h : Lit D) (F : Forest S.ratio) (A : Stores S) (k : S.Choices) (s : ℝ) (hi : D.Nonoverlap b) : Programme (packets D F k₀ A k h) b where
  physical := hi
  required := kept D (chosen D F k₀ A k) b
  paying := tapped D (chosen D F k₀ A k)
  layer i := timing (historical D (chosen D F k₀ A k) i)
  stored := stores D b (chosen D F k₀ A k)
  posted := topcard D b (chosen D F k₀ A k)
  first := precedence D k₀ b h.toApp
  original V p i := bill D k₀ b h V p i
  constPage V p i := attached D k₀ b h V p i
  keep := preserves D k₀ b h
  fine i he := (stays D _).mpr (cost_here D i he).2
  noise i he := (stays D _).mpr (aisle_here D i he)
  inherit i := (stays D _).mpr trivial
  rawG _ := solitary _
  rawLog i := Parcel.columns D b (chosen D F k₀ A k) i s
end YM.PhysicalNext.Dictionary.Parcel
