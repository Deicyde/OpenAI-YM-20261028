import YM.Next.FREE_KERNELS.Sell



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Periodic identities of lifted kernels from a cofinal family of meshes

Needed because Rack/FlatBill/Pins only ask some of the *physical*
identities (those involving StepData/op) at periods of the issued calendar.
We want to pass even to the unissued tori, e.g. to use limiting Fourier/
translation kernel identities or repin at other torus tests without changing
H AND any of the stack rows. Use the entry Tannery lemma in `Free.Bank`,
along our cofinal series at EACH fixed step. Pure absolute Row algebra here,
for single scale and Cross with an actual L fixed (no history changes and no
pricing from this lemma). Covers need same L, proof handles all sizes. Doesn't
support say changing an ell path sum after evaluating, nor transferring arbitrary
density estimates to another period just from convergence. Applied to Wired in
`Tori`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels.Echo
open Filter Function Lattice RG RG.Supply Wilson Precision Craft Laurent Exterior Bloch Matrix
open Next.Free Work.F08
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {ι κ ν : Type*} {L : Side}

/-- Same scale. -/
abbrev Family (ι κ : Type*) := ∀ c : Side, Matrix (Co c ι) (Co c κ) ℝ

def Sound (F : Family ι κ) := ∃ R : Row ι κ, Whole R ∧ ∀ c, F c = R.acts c

lemma heard {R : Row ι κ} (h : Whole R) : Sound R.acts := ⟨R,h,fun _ => rfl⟩

lemma Sound.transpose {F : Family ι κ} (h : Sound F) : Sound (fun c => (F c).transpose) := by
  obtain ⟨R,hR,hq⟩ := h; exact ⟨transRows R,hR.flipped,fun c => by simp only [acts_trans,hq]⟩
lemma Sound.multiply [Fintype κ] {F : Family ι κ} (h : Sound F) {K : Family κ ν} (g : Sound K) :
    Sound (fun c => F c * K c) := by
  obtain ⟨R,hR,hp⟩ := h; obtain ⟨Q,hQ,hq⟩ := g
  exact ⟨composeRows R Q,hR.prod hQ,fun c => by simp only [hp,hq,hR.acts hQ]⟩
lemma Sound.plus {F H : Family ι κ} (hf : Sound F) (hh : Sound H) : Sound (fun c => F c + H c) := by
  obtain ⟨R,hR,hp⟩ := hf; obtain ⟨Q,hQ,hq⟩ := hh
  exact ⟨plusRows R Q,hR.plus hQ,fun c => by simp only [hp,hq,hR.acts_plus hQ]⟩
lemma Sound.minus {F H : Family ι κ} (hf : Sound F) (hh : Sound H) : Sound (fun c => F c - H c) := by
  obtain ⟨R,hR,hp⟩ := hf; obtain ⟨Q,hQ,hq⟩ := hh
  exact ⟨minusRows R Q,hR.minus hQ,fun c => by simp only [hp,hq,hR.less hQ]⟩
lemma Sound.scales {F : Family ι κ} (hf : Sound F) (x : ℝ) : Sound (fun c => x • F c) := by
  obtain ⟨R,hR,hp⟩ := hf; exact ⟨scaleRows x R,hR.weight _,fun c => by simp only [hp,acts_scale]⟩
lemma Sound.stack {F : Family ι ν} {H : Family κ ν} (hf : Sound F) (hh : Sound H) :
    Sound (fun c => Craft.stack (F c) (H c)) := by
  obtain ⟨R,⟨a,C,ha,hC⟩,hp⟩ := hf; obtain ⟨Q,⟨b,D,hb,hD⟩,hq⟩ := hh
  exact ⟨stackRows R Q,⟨min a b,max C D,lt_min ha hb,strip_stack
    (strip_mono hC (min_le_left ..) le_rfl) (strip_mono hD (min_le_right ..) le_rfl)⟩,fun c => by simp only [hp,hq,acts_stack]⟩
lemma oneSound (ι : Type*) [DecidableEq ι] : Sound (fun _ => 1 : Family ι ι) :=
    ⟨unitRow _, Whole.coin _,fun c => (acts_unit c).symm⟩
lemma noneSound (ι κ : Type*) : Sound (fun _ => 0 : Family ι κ) := ⟨0,barren_whole,fun c => (barren_acts c).symm⟩
lemma fullSound {M : Bed} (hm : Whole M.roots) (p : Clip) : Sound (M.full p) :=
    ((oneSound (TypeFace 2)).scales (Real.sqrt p.direct)).stack (heard hm)
lemma dSound (k : ℕ) : Sound (fun c => d k c : Family (TypeFace (k+1)) (TypeFace k)) := heard (Whole.boundary k)
lemma kSound {F : Family (TypeFace 2) (TypeFace 2)} (h : Sound F) : Sound (fun n => Precision.K (F n) : Family (TypeFace 1) (TypeFace 1)) :=
    (((dSound 1).transpose.multiply h).multiply (dSound 1))

private lemma cofinal_rows {P Q : Row ι κ} (hP : Whole P) (hQ : Whole Q) {c : ℕ → Side}
    (hn : Tendsto (fun i => (c i).val) atTop atTop) (he : ∀ i, P.acts (c i)=Q.acts (c i)) : P=Q := by
  funext i j x
  have hh := entry_limit c hn P hP.safe i j x
  simp_rw [he] at hh
  exact tendsto_nhds_unique hh (entry_limit c hn Q hQ.safe i j x)

lemma all {F H : Family ι κ} (hf : Sound F) (hh : Sound H) (c : ℕ → Side)
    (hn : Tendsto (fun i => (c i).val) atTop atTop) (he : ∀ i, F (c i) = H (c i)) (y : Side) : F y=H y := by
  obtain ⟨R,hR,hr⟩ := hf; obtain ⟨Q,hQ,hq⟩ := hh
  simp_rw [hr,hq] at he ⊢
  rw [cofinal_rows hR hQ hn he]

/-- FINE × COARSE kernels with L. Need covers only Lipschitz under fixed L
prices (here already available as Whole). -/
abbrev Link (L : Side) (ι κ : Type*) := ∀ c f : Side, f.val=c.val*L.val → Matrix (Co f ι) (Co c κ) ℝ
abbrev vertical (L : Side) (c f : Side) (h : f.val=c.val*L.val) : Ratio c f := ⟨L,h⟩
abbrev listens {S : Side} (A : Cross S ι κ) : Link S ι κ := fun c f h => installed (vertical S c f h) A

def Across {S : Side} (F : Link S ι κ) := ∃ A : Cross S ι κ, Whole A ∧ ∀ c f h, F c f h=listens A c f h

lemma heardAcross {A : Cross L ι κ} (ha : Whole A) : Across (listens A) := ⟨A,ha,fun _ _ _ => rfl⟩
lemma Across.then [Fintype κ] {F : Link L ι κ} (h : Across F) {H : Family κ ν} (he : Sound H) :
    Across (S:=L) (fun c f h => F c f h * H c) := by
  obtain ⟨A,hA,ha⟩ := h; obtain ⟨R,hR,hr⟩ := he
  exact ⟨composeRows A R,hA.prod hR,fun c f h => by simp only [ha,hr,listens,hA.from_coarse (vertical L c f h) hR]⟩
lemma Across.from [Fintype κ] {F : Link L κ ν} (h : Across F) {H : Family ι κ} (he : Sound H) :
    Across (S:=L) (fun c f h => H f * F c f h) := by
  obtain ⟨A,hA,ha⟩ := h; obtain ⟨R,hR,hr⟩ := he
  refine ⟨fineCompose R A,?_,fun c f h => ?_⟩
  · obtain ⟨a,C,h₁,h₂⟩ := hA; obtain ⟨b,D,h₃,h₄⟩ := hR
    exact ⟨min a b,_,lt_min h₁ h₃,strip_fine (lt_min h₁ h₃).le (strip_mono h₄ (min_le_right ..) le_rfl)
      (strip_mono h₂ (min_le_left ..) le_rfl)⟩
  simp only [ha,hr,listens,hR.from_fine (vertical L c f h) hA]

lemma allAcross {F H : Link L ι κ} (hf : Across F) (hh : Across H) (c f : ℕ → Side)
    (h : ∀ i, (f i).val=(c i).val*L.val) (hn : Tendsto (fun i => (c i).val) atTop atTop)
    (he : ∀ i, F (c i) (f i) (h i)=H (c i) (f i) (h i)) (x y : Side) (hx : y.val=x.val*L.val) :
    F x y hx=H x y hx := by
  obtain ⟨A,hA,ha⟩ := hf; obtain ⟨B,hB,hb⟩ := hh
  simp_rw [ha,hb,listens] at he ⊢
  have hh (i) := he i
  have hR (j : ℕ) : A.acts (c j)=B.acts (c j) := by
    ext i k
    have h := congr_fun (congr_fun (hh j) ((splitCo (vertical L (c j) (f j) (h j)) ι).symm i)) k
    simpa only [installed,Matrix.submatrix_apply,id_eq,Equiv.apply_symm_apply] using h
  rw [cofinal_rows hA hB hn hR]

lemma schedule_sides (S : Schedule) (m : ℕ) : Tendsto (fun p => (S.side m p).val) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_mul_of_one_le_right (Nat.zero_le _) (S.denominator m).property) S.period_strict.tendsto_atTop
end YM.UVNext.PricedKernels.Echo
