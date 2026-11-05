import YM.Push.LOCAL_SPLITTING.Initial
import YM.Push.LOCAL_SPLITTING.Step

/-!
# Common dictionary consumer at Paper.Clocks

Given the *pre-split* outputs and leading-model estimates (Output) on the
actual pushes with actual vacuum activities, assemble on THAT history.

No
`remBound` on converted sources assumed.

Includes the boundary case of no
steps.

This isolates localization, bulk/forced and perturbation estimates that
the component kernel expansion still needs to provide, and the numerical
prices/delay/alphabet premises.

Same parameters and labels
across budgets and uses of a column.

No auxiliary symmetry on a separately
optimized reference read is assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels Next.Foundations Work.G08 Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {d k N p : ℕ} {F : Labels.Frame G d} {H : RG.History G} {A : Hol G} {T : SectionData F}

/-- Raw pre-projection expansion data, with slots that *can be supplied* in
particular given `Nonempty (Reserve ...)` from the same vacuum. No requirement
of unused slots on `rep` at indices outside the range being considered.
-/
structure PreData (T : SectionData F) (H : RG.History G) (k N p : ℕ) where
  X (i : ℕ) : ℕ → Support (H.S.side i p)
  M (i : ℕ) : F.Coeff → Raw F (H.S.side i p)
  slots i : k ≤ i → i<N → Slots (H.rep N p i).activities (fun j => joint T 0 (X i j))
  launch : Slots (H.rep N p N).activities (fun _ : Unit => T.footprint 0)

variable {n : Side}
/-- Symmetry estimates on the RAW dictionary, not just on re-fitted columns. -/
structure Aligned (T : SectionData F) (X : ℕ → Support n) (K : F.Coeff → Raw F n) : Prop where
  linear : Raw.Linear K
  real v : (K (star v)).seed = star (K v).seed ∧ ∃ e : Equiv.Perm ℕ, ∀ i, X (e i) = X i ∧ (K (star v)).bulk (e i) = star ((K v).bulk i)
  signed v (s : Signed) : (K (F.act s.ortho v)).seed = F.act s.ortho (K v).seed ∧ ∃ e : Equiv.Perm ℕ, ∀ i,
    X (e i) = (X i).image (affine s 0) ∧ (K (F.act s.ortho v)).bulk (e i) = (K v).bulk i ∘ pull s 0

namespace PreData
variable (Z : PreData T H k N p)

def init (A : Hol G) (m : ℕ) (v : F.Coeff) : Coefficient F (H.S.side m p) :=
  if he : m=N then he.symm ▸ Bare.make T (H.rep N p N) 0 Z.launch v
  else if h : k≤m ∧ m<N then (Z.M m v).build 0 (Z.X m) A T (H.rep N p m) (Z.slots m h.1 h.2) else ⟨0,fun _ => ∅,0,0⟩

theorem top (v : F.Coeff) : Z.init A N v = Bare.make T (H.rep N p N) 0 Z.launch v := by simp only [init, ↓reduceDIte]
theorem lower (i) (hi : k ≤ i) (he : i<N) (v : F.Coeff) : Z.init A i v = (Z.M i v).build 0 (Z.X i) A T (H.rep N p i) (Z.slots i hi he) := by rw [init,dif_neg he.ne,dif_pos ⟨hi,he⟩]

def pay (A : Hol G) (W : Worth) (m : ℕ) (v : F.Coeff) :=
  if h : m<N then nextCash H F m W (Z.init A (m+1) v).x (pay A W (m+1) v) else F.coeffSize (F.core v)
termination_by N-m

lemma pay_pos (A : Hol G) (W : Worth) (m : ℕ) (v : F.Coeff) : 0 ≤ Z.pay A W m v := by
  rw [pay]; split
  · unfold nextCash; have hi := (H.S.block m).property
    exact add_nonneg (mul_nonneg (zero_le_one.trans (W.prices _)) (size_nonneg F _)) (mul_nonneg (by unfold barunit puffs; positivity) (pay_pos A W (m+1) v))
  exact size_nonneg ..
termination_by N-m

def paper (A : Hol G) (W : Worth) : Paper H N p F where
  inits := Z.init A
  paid := Z.pay A W

structure Verified (A : Hol G) (W : Worth) (w : ℕ → ℝ) : Prop where
  ahead : k ≤ N
  conv i : k ≤ i → i ≤ N → H.Conv N p i
  funded i : k ≤ i → i ≤ N → Readable A T (H.rep N p i).p (H.S.side i p) (w i)
  width i : k ≤ i → i<N → hitWidth (H.levels.budget i)*kappa H i ≤ 1
  delay : BareDelay T (H.rep N p N).p (H.levels.clock.forcedAllowance N)
  aligned i : k ≤ i → i<N → Aligned T (Z.X i) (Z.M i)
  outputs i : k ≤ i → i<N → ∀ v, ∃ σ D q ε, Prices A T H i W (w i) σ D q ε ∧
    Output A T H N p i 0 (Z.init A (i+1) v) (Z.pay A W (i+1) v) (Z.X i) (Z.M i v) σ D q ε

private theorem parent_zero (H : RG.History G) (i p : ℕ) : (H.levels.clock.op i p).ratio.parent 0 = 0 := by
  let r := (H.levels.clock.op i p).ratio
  exact (show r.embed 0 = 0 from r.root.map_zero) ▸ r.embed_parent 0

variable {Z} {W : Worth} {w : ℕ → ℝ}
private theorem verified_step (h : Z.Verified A W w) (i : ℕ) (hi : k ≤ i) (he : i<N) (v : F.Coeff) :
    let P := Z.paper A W
    let t := P.paid (i+1) v
    let Q := P.inits i v
    Q.Format 0 A (H.rep N p i) ∧ Q.remBound 0 (H.rep N p i) (kappa H i) (P.paid i v) ∧
      Q.density 0 T (H.rep N p i) = ((H.S.block i).val : ℂ)^d • (H.levels.clock.op i p).push (H.β N p (i+1)) ((P.inits (i+1) v).density 0 T (H.rep N p (i+1))) ∧ localOwns H i W F Q.x (P.inits (i+1) v).x t := by
  obtain ⟨σ,D,q,ε,hv,hQ⟩ := h.outputs i hi he v
  have hg (S) := one_step hQ hv (Z.pay_pos A W (i+1) v) S (h.conv i hi he.le) (h.funded i hi he.le) (h.width i hi he)
  dsimp only at hg; rw [parent_zero] at hg
  dsimp only [paper]; rw [pay, dif_pos he, Z.lower i hi he]; exact hg _

private theorem dictionaries (h : Z.Verified A W w) (i : ℕ) (hi : k ≤ i) (he : i<N) :
    (∀ v, (Z.M i v).Format 0 (Z.X i) (H.rep N p i)) ∧ (∀ v, Summable ((Z.M i v).row 0 (Z.X i) A (H.rep N p i).p.threshold)) := by
  suffices ∀ v, (Z.M i v).Format 0 (Z.X i) (H.rep N p i) ∧ Summable ((Z.M i v).row 0 (Z.X i) A (H.rep N p i).p.threshold) by exact ⟨fun v => (this v).1,fun v => (this v).2⟩
  intro v; obtain ⟨_,_,_,_,h1,h2⟩ := h.outputs i hi he v
  have hf := h.funded i hi he.le
  have ht := Raw.dominated_pieces _ hf h2.raw (h2.income h1 (Z.pay_pos ..) (h.conv i hi he.le) hf (h.width i hi he)) |>.1.of_norm
  simpa only [parent_zero] using And.intro h2.raw ht

theorem clocks (h : Z.Verified A W w) : (Z.paper A W).Clocks T A W k := by
  have hc := h.conv N h.ahead le_rfl
  have hs := (h.funded N h.ahead le_rfl).sound
  refine ⟨h.ahead,fun i hi hm v => ?_,fun v => ?_,fun i hi hm v => ?_,fun i hi hm v => (verified_step h i hi hm v).2.2.1,?_,fun v => by simp [paper,top,Bare.make],fun i hi hm => ?_,fun i hi hm => ?_,fun i hi hm v => ?_⟩
  · rcases eq_or_lt_of_le hm with rfl|hm
    · simp only [paper,top,pay,lt_self_iff_false, ↓reduceDIte]; exact ⟨Bare.format hs hc.good.labels.forced v, thick hs v hc.good.labels.boundK (Real.exp_pos _) h.delay⟩
    have hv := verified_step h i hi hm v; exact ⟨hv.1,hv.2.1⟩
  · simp only [paper,pay,lt_self_iff_false,↓reduceDIte, le_refl]
  · have hx := (verified_step h i hi hm v).2.2.2.1
    dsimp only [paper]; rw [pay,dif_pos hm]; exact hx
  · intro v U; simp only [paper,top]; exact charges H N p hc hs v U
  · let v := unitVec F H N
    suffices he : (Z.init A i v).x = unitVec F H i ∧ Z.pay A W i v = 0 from he.1
    induction hm using Nat.decreasingInduction with
    | self => simp only [pay,lt_self_iff_false,↓reduceDIte,Z.top,Bare.make,v,unitVec,map_smul,show F.core F.e0 = 0 from funext fun i => by by_cases h : i=0 <;> simp [Frame.e0,Frame.core,update,h]]; simp [Frame.coeffSize]
    | of_succ j hj ih =>
      obtain ⟨hv,hp⟩ := ih (hi.trans j.le_succ)
      rw [pay, dif_pos hj]; exact (verified_step h j hi hj v).2.2.2.2 hv hp
  · rcases eq_or_lt_of_le hm with rfl|hm
    · simp only [paper,top]; exact Bare.linear
    simp only [paper, Z.lower i hi hm]
    have hd := dictionaries h i hi hm
    exact Raw.build_linear _ (h.funded i hi hm.le) (h.aligned i hi hm).linear hd.1 hd.2
  rcases eq_or_lt_of_le hm with rfl|hm
  · simp only [paper,top]; exact ⟨rfl, fun _ => rfl⟩
  have hd := dictionaries h i hi hm
  have ht := h.aligned i hi hm
  have hf := h.funded i hi hm.le
  simp only [paper,Z.lower i hi hm]; obtain ⟨hv,e,he⟩ := ht.real v
  refine ⟨Raw.build_star _ hf (hd.1 v) hv e (fun i => (he i).1) (fun i => (he i).2),fun s => ?_⟩
  obtain ⟨hv,e,he⟩ := ht.signed v s
  have hk (S') := Raw.build_pull (Z.slots i hi hm) s 0 (R':=H.rep N p i) S' hf (hd.1 v) rfl ((by decide : 2 ≤ 4).trans (actual_side_ge H.S i p)) (hd.2 v) hv e (fun i => (he i).1) (fun i => (he i).2)
  rw [show turnSites (n:=H.S.side i p) s 0 0 = 0 from by change affine s (0 : Site (H.S.side i p)) 0 = _; simp [affine]] at hk
  exact hk _
end PreData
end YM.Push.Local
