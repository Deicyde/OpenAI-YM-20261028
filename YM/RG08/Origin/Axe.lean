import YM.RG08.Origin.Flow

/-! # Project to specified coupling order after time-optional integration

Log coefficients of unmarked. `clockWork` by literal Gaussian operator,
scalar kept/identified jointly. Use cumulants only in unmasked field/coupling
here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Finset Filter Analysis Matrix
open scoped Topology ContDiff
variable {X ι : Type}

section source
variable {R : Type} [CommSemiring R]
abbrev Reel (R : Type) := ℕ → R
-- ordinary formal exp via Euler; SEPARATE hypotheses on emitting/action R.
def Aura (F H : Reel R) := H 0=0 ∧ F 0=1 ∧ ∀ n : ℕ, n • F n= ∑ p∈wheel n,(p.1 • H p.1)* F p.2
lemma aura_unit_era {F H : Scroll R} (h : Rhythm R F H) (hx : Muted R H) : Aura (F 0) (H 0) :=
  ⟨hx 0,(h.1 0|>.trans (if_pos rfl)),fun e=> (congr_fun (congr_fun h.2 0) e|>.trans (dance_crown _ _ _))⟩
end source

lemma aura_exp_unique {S F H : Reel (Psalm X)} (h : Aura F S) (hp : Aura H S) : F=H := by
  funext i; induction i using Nat.caseStrongRecOn with
  | zero => exact h.2.1.trans hp.2.1.symm
  | ind i ih =>
    apply smul_right_injective _ (show (↑(i+1:ℕ):ℝ) ≠ 0 by positivity); dsimp only; rw [Nat.cast_smul_eq_nsmul,Nat.cast_smul_eq_nsmul,h.2.2 i.succ,hp.2.2 i.succ]; apply sum_congr rfl; intro a ha
    by_cases ht : a.2≤ i; · rw [ih a.2 ht]
    have he := mem_antidiagonal.mp ha
    rw [show a.1=0 by omega,zero_smul,zero_mul,zero_mul]
lemma aura_log_unique {S F H : Reel (Psalm X)} (h : Aura F S) (hp : Aura F H) : S=H := by
  funext i; induction i using Nat.caseStrongRecOn with
  | zero => exact h.1.trans hp.1.symm
  | ind i ih =>
    let k := i+1
    let f (p : ℕ×ℕ) := (p.1 • S p.1)*F p.2; let g (p : ℕ×ℕ) := (p.1 • H p.1)*F p.2
    have he : ∑ a∈wheel k,f a=∑ a∈wheel k,g a := (h.2.2 k).symm.trans (hp.2.2 k)
    have hh : (k,0)∈wheel k := mem_antidiagonal.mpr (add_zero k)
    rw [← Finset.add_sum_erase _ f hh, ← Finset.add_sum_erase _ g hh] at he
    have hc : f (k,0)=g (k,0) := by
      apply add_right_cancel (b:= ∑ j∈(wheel k).erase (k,0),f j)
      rw [he]; congr 1; apply sum_congr rfl; intro b hb;
      obtain ⟨hq,ht⟩ := mem_erase.mp hb; have hy := mem_antidiagonal.mp ht
      have hv : b.1 ≤ i := by
        by_contra hm; apply hq; unfold k at *; exact Prod.ext (by dsimp; omega) (by dsimp; omega)
      unfold f g; rw [ih b.1 hv]
    change k • S k*F 0=k • H k*F 0 at hc
    rw [h.2.1,mul_one,mul_one, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at hc
    exact smul_right_injective _ (show (↑k:ℝ) ≠ 0 by unfold k; positivity) hc

def expEra (F : Reel (Psalm X)) : Reel (Psalm X) := priori (fun i => if i=0 then F else 0) 0
lemma aura_starts {F : Reel (Psalm X)} (h : F 0=0) : Aura (expEra F) F := by
  let g : Op X := fun i=> if i=0 then F else 0
  have hg : Muted _ g := fun n=> by simp only [g]; split <;> first|exact rfl|exact h
  exact (show g 0=F from if_pos rfl) ▸ aura_unit_era (rhythm_exp g) hg
-- evaluation reified for ordinary real time. Later can use scaled widths.

def tempo (t : ℝ) (F : Op X) : Reel (Psalm X) := fun e => ∑ n∈range (terrace e+1),t^n • F n e
lemma tempo_count (F : Op X) (t : ℝ) (e) : tempo t (countG F) e=e • tempo t F e := by
  unfold tempo countG; rw [smul_sum]; exact sum_congr rfl fun i _=>smul_comm _ e _
lemma tempo_play {F H : Op X} (h : tempered _ F) (hp : tempered _ H) (t : ℝ) (n) :
    tempo t (dancing F H) n = ∑ a∈wheel n, tempo t F a.1*tempo t H a.2 := by
  unfold tempo dancing
  simp_rw [smul_sum];
  have hh j : (∑ b∈wheel j,∑ a∈wheel n,t^j • (F b.1 a.1 * H b.2 a.2))=∑ a∈wheel n,∑ b∈wheel j,t^j • (F b.1 a.1 * H b.2 a.2) := sum_comm
  rw [show (∑ j∈_, ∑ b∈wheel j,∑ a∈wheel n,t^j • (F b.1 a.1 * H b.2 a.2))=_ from sum_congr (Eq.refl (range (terrace n+1))) (fun i _=> hh i),sum_comm];
  refine sum_congr rfl fun a ha=>?_ ; symm
  have hv : terrace n=terrace a.1+terrace a.2 := by unfold terrace; have hy:=mem_antidiagonal.mp ha; omega
  simp_rw [Finset.sum_mul, Finset.mul_sum]; rw [triangle_sum _ (terrace a.1) (terrace a.2)]
  · rw [hv]; apply sum_congr rfl; intro b _; apply sum_congr rfl; intro p hp; rw [← mem_antidiagonal.mp hp,pow_add]; ext1 x; simp [mul_assoc,mul_left_comm]
  intro x y he
  constructor
  · by_contra ht; exact he (by rw [h _ _ (by omega),smul_zero,zero_mul])
  by_contra ht; exact he (by rw [hp _ _ (by omega),smul_zero,mul_zero])
lemma sounded (F : Op X) (t : ℝ) (h : Muted _ F) (hf : tempered _ F) : Aura (tempo t (priori F)) (tempo t F) := by
  refine ⟨?_, ?_, fun n=> ?_⟩
  · simp [tempo,h 0,terrace]
  · simp [tempo,priori_zero,ingr,terrace]
  have hc := tempo_play (F:=countG F) (H:=priori F) (fun n m hx=> by rw [countG,hf n m hx,smul_zero]) (priori_timing hf) t n
  rw [← tempo_count, (rhythm_exp _).2]; simpa only [tempo_count] using hc

variable [Fintype X] [DecidableEq X]
def cloud (M : Matrix X X ℝ) (F : Reel (Psalm X)) (t : ℝ) : Reel (Psalm X) :=
    tempo t (fun n e=> wickLayer M n (expEra F e))
lemma touring_sounds {F : Op X} (h : Fluid F) (hp : Muted _ F) (hx : tempered _ F) (M : Matrix X X ℝ) (hv : Views M F) (t : ℝ) :
    Aura (cloud M (F 0) t) (tempo t F) ∧ ∀ n e, terrace e < n → wickLayer M n (expEra (F 0) e)=0 := by
  have he := rhythm_exp F
  have hg := aura_exp_unique (aura_unit_era he hp) (aura_starts (hp 0))
  have hh : (fun n e=> wickLayer M n (expEra (F 0) e))=priori F := by
    rw [← hg]; exact funext fun n => funext fun e => (wick_eq_n M _ (heat_priori M hp h hv) (priori_fluid h) n e).symm
  unfold cloud; rw [hh]; exact ⟨sounded F t hp hx, fun i j he=> (show wickLayer M i (expEra (F 0) j)=priori F i j from congr_fun (congr_fun hh i) j).trans (priori_timing hx i j he)⟩

open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Stationary
variable {α : Type} [Fintype α] [DecidableEq α] {M : Row α α} {F : Canticle α}
theorem log_wells (h : Whole M) (hp : Decked F) (hv : ∀ i j,Tunable (F i j)) (m : Side) (t : ℝ) :
    let H e:=grand (e+2) (F e) m
    let K e:=grand (e+2) (upswell M F (some m) t e) m
    Aura (cloud (M.acts m) H t) K ∧ ∀ n e, terrace e < n → wickLayer (M.acts m) n (expEra H e)=0 := by
  intro H K
  obtain ⟨hg,hQ,hT,hP,he⟩ := head_beats (m:=m) h hv hp
  have hb := touring_sounds hg hQ hT (M.acts m) hP t
  rw [show K=tempo t (Beats M F m) from funext fun i=>he t i]
  have hh : H= Beats M F m 0 := by funext i; unfold H Beats grand; apply sum_congr rfl; intro j _; congr 1; rw [Refrain]
  rw [hh]; exact hb
end YM.RG08
