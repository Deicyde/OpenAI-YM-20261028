import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
/-!
 # Book skeleton at X.Band and Revenues. Keep E6 Houses supports for unchanged bills,
 true Halo and Deep support numbering; padded Nat blanks for loose (anchored, orbit invariant).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open Refrain Trio
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {B : BudgetPoint} {X : Listing G c} (C : Listing G c) (z w : ℕ)
abbrev Door (c : Side) := Seat c × Site c
abbrev leap (b : ℕ) (i:Site c): RegularAddress c:= ⟨i, neighbors b i,(neighbors_mem ..).2 (by simp)⟩
abbrev sea (b:ℕ) (i: Door c): RegularAddress c := Song.revolve (leap b) i
abbrev Civ (c : Side):= ℕ ⊕ Door c
def leanU (c : Side) := numbering (Civ c)
-- Trace duplication only in separate Σ at orbit, no period price. soft unoccupied Left includes site zeros at coordinates `X.reg`.
def lodge : Pipes G c where
  reg := Sum.elim C.reg (sea z) ∘ leanU c
  kernel := C.hard
  softer := RegularAddress.support ∘ Sum.elim C.reg (sea w) ∘ leanU c
  sites i:= ⟨_, (Sum.elim C.reg (sea w) (leanU c i)).anchor⟩
variable {d : Tap G c} {e p v : ℝ}
def bison (V:Collection.Source G c) (g t:Trio.Offer G c): Tap G c:= ⟨Sum.elim V.logRead (choir g) ∘ leanU c, V.hardRead, Sum.elim (fun _=> 0) (choir (-t)) ∘ leanU c⟩ -- negative EXACT sign

section trans
variable (V:Collection.Source G c) (g t:Trio.Offer G c) (s : Signed) (b : Site c) (h : (C.read V).Moves s b)
local notation "d" => (bison V g t)
local notation "ℒ" => (lodge C z w)
abbrev reel (v:Equiv.Perm ℕ) : Equiv.Perm (Civ c):= Equiv.sumCongr v (whirl s b)
include h
lemma reeds : Nonempty (((ℒ).pours (bison V g t)).Moves s b) := by
  let X:=d; let P:=ℒ; let y:=leanU c; let e:=reel s b h.ep; let q:=congo y e
  have hk i:y (q i)=e (y i):= perch y e i
  let f : Civ c→RegularAddress c:= Sum.elim C.reg (sea z); let u:=Sum.elim V.logRead (Song.choir g)
  have hm i : (f (e i)).support = (f i).support.image (Lattice.affine s b)∧ (f (e i)).site=Lattice.affine s b (f i).site ∧ u (e i)= u i ∘ pull s b:= by
    rcases i with i|i
    · exact ⟨h.reg_support i,h.reg_site i,funext (h.valuesE _)⟩
    obtain ⟨h₁,h₂,h₃⟩:= spirit (leap z) g s b i; exact ⟨h₂,h₁,h₃⟩
  exact ⟨⟨q,h.kp,(fun i=> (hk i).symm ▸ ((hm (y i)).2.1) : ∀ i,(f (y (q i))).site=_), (fun i=> by change (f (y (q i))).support=_; rw [hk]; exact (hm (y i)).1),h.forced_support,h.forced_inventory,h.forced_tests,(fun i V=> by change u (y (q i)) V=_; rw [hk]; exact congr_fun (hm (y i)).2.2 V),h.valuesK⟩⟩ -- syntax notation

lemma gander : ∃ v:Equiv.Perm ℕ,(∀ i, (ℒ).softer (v i)= (lodge C z w|>.softer i).image (Lattice.affine s b)) ∧ ∀ U i,(bison V g t|>.logarithm (v i)) U = (d).logarithm i (pull s b U):= by
  let e:= leanU c; let v:= reel s b h.ep; refine ⟨Refrain.congo e v,fun i=> ?_,fun U i=>?_⟩
  · change (Sum.elim C.reg (sea w) (e _)|>.support)=_; rw [perch]
    suffices hh:∀ i,(Sum.elim C.reg (sea w) (v i)|>.support) = (Sum.elim C.reg (sea w) i|>.support).image (Lattice.affine s b) from hh (e i)
    rintro (i|i); · exact h.reg_support i
    exact (spirit (leap w) g s b i).2.1
  let f : Civ c→ Config G c→ℝ:=Sum.elim (fun _=>0) (choir (-t)); change f (e _) U=_; rw [perch]
  suffices hh : ∀ i,f (v i) U= f i (pull s b U) from hh _
  rintro (j|j); · rfl
  exact congr_fun ((spirit (leap w) (-t) s b j).2.2) U
omit h
lemma reg_bison {e v : ℝ} (H : Meadow.Budget B C.reg V.logRead e) (hp: Meadow.Budget B (leap z) g v) : Meadow.Budget B (lodge C z w).reg (bison V g t|>.regular) (e+turnFee B*v):= by
  obtain ⟨k,h,hk⟩:=H; obtain ⟨a,hA,ha⟩:=hp
  obtain ⟨he,hv⟩:= Song.spiral _ g a (fun i=>(ha i).1) (fun i=>(ha i).2) hA
  refine ⟨Sum.elim k (fun i:Door c=>Rim c*(turnFee B*a i.2)) ∘ leanU c,fun i=>Cost.equiv (leanU c) (Cost.sum (f:=fun j:Civ c=> if (Sum.elim C.reg (sea z) j|>.site)=i then Sum.elim k (fun i:Door c=>Rim c*(turnFee B*a i.2)) j * Real.exp (preExponent B*coverNumber B.B (Sum.elim C.reg (sea z) j|>.support)) else 0) (h i) (hv i)),?_⟩ -- inference help
  suffices hh : ∀ i, B.Regular (Sum.elim C.reg (sea z) i|>.support) (Sum.elim V.logRead (choir g) i) ∧ B.supBounds (Sum.elim C.reg (sea z) i|>.site) (Sum.elim C.reg (sea z) i|>.support) (Sum.elim V.logRead (choir g) i) (Sum.elim k (fun i:Door c=> Rim c*(turnFee B*a i.2)) i) from fun i=>hh (leanU c i)
  rintro (i|i); · exact hk i
  exact he i

-- lore with sign Defeq real scales.
variable (hh:∀ i:Site c, Trio.Tidy B (neighbors w i) (t i))
include hh
lemma estateP : ∀ i,Trio.Tidy B ((ℒ).softer i) ((bison V g t).logarithm i):= by
  suffices hk: ∀ i, Trio.Tidy B (Sum.elim C.reg (sea w) i|>.support) (Sum.elim (fun _=>0) (choir (-t)) i) from fun i=> hk (leanU c i)
  rintro (i|⟨u,i⟩)
  · exact Trio.tidy_const _ _
  have hx : Trio.Tidy B (u.spread (neighbors w i)) (t i ∘ u.view):= ⟨Push.Local.uses_pull ((hh _).uses) _ _, (hh i).borel.comp (continuous_pull ..).measurable, Push.Local.invariant_pull (hh _|>.invariant) _ _⟩
  let g:=t i ∘ u.view; exact Trio.tidy_scale _ _ (show Trio.Tidy B _ (-g) from by rw [← zero_sub g]; exact Trio.tidy_sub _ (Trio.tidy_const B _) hx)
omit hh
lemma failedP (h:∀ i U, t i U ≠ 0→ ¬Healthy B.threshold (neighbors w i) U):∀ i U,(d).logarithm i U≠0→¬Healthy B.threshold ((ℒ).softer i) U:= by
  suffices hh:∀ i U, Sum.elim (fun _=> (0:Config G c→ℝ)) (choir (-t)) i U ≠0→¬Healthy B.threshold (Sum.elim C.reg (sea w) i|>.support) U from fun i=>hh (leanU c i)
  rintro (i|⟨v,i⟩) U ht hU
  · exact ht rfl
  refine h _ _ (fun hp=> ht ?_) ((v.healthy ..).mp hU)
  change Rim c * (-(t i (v.view U)))=_; rw [hp,neg_zero,mul_zero]
end trans
end YM.PhysicalNext.Repeat.Marlin
