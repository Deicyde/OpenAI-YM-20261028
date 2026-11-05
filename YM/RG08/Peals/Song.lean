import YM.RG08.Peals.Duet

/-! # Rooted connected-log heat coefficients

`τ^n g^e`, ordinary coefficients; valence after integrations at
that point graded separately. Expression works on actual cover and also on
all specified finite grids. Requirements on covariance in separate budget.
Keep rank zero. Finite locally, n>L(e) vanishes by valence. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {α : Type} {σ A C : ℝ} {n r d e : ℕ} {M : Row α α}

abbrev Verse (α : Type) := (r : ℕ) → Shale α r
abbrev Canticle (α : Type) := ℕ → Verse α

-- totalized rank cast on antidiagonal; use only there for sums
def prolong (R : ℕ) (u : Shale α r) : Shale α R := if h : r=R then h ▸ u else 0
lemma prolong_self (u : Shale α r) : prolong r u=u := by simp [prolong]
lemma prolong_zero (n r) : prolong n (0:Shale α r)=0 := by
  by_cases h:r=n; · rw [h]; exact prolong_self _
  rw [prolong,dif_neg h]

private abbrev Rsum := Finset.HasAntidiagonal.antidiagonal (A:=ℕ)

def symphony (M : Row α α) (V W : Verse α) (r : ℕ) := ∑ a∈Finset.antidiagonal r,
      prolong r (medley M (V (a.1+1)) (W (a.2+1)))

-- full E-grade products (no underflow convention)
def Refrain (M : Row α α) (f : Canticle α) (p : Option Side) (n : ℕ) (e r : ℕ) : Shale α r := match n with
  | 0 => f e r
  | n+1 => (↑(n+1:ℕ):ℝ)⁻¹ • (chirp M p (Refrain M f p n e (r+2)) + (1/2:ℝ) • ∑ b : {b : ℕ×ℕ // b∈Rsum n},∑ a∈Finset.antidiagonal e,
                symphony M (fun r=>Refrain M f p b.val.1 a.1 r) (fun r=> Refrain M f p b.val.2 a.2 r) r)
termination_by n
decreasing_by
  all_goals (first|omega| (have hh : b.val.1+b.val.2=n := mem_antidiagonal.mp b.property; omega))

lemma Refrain_step (M : Row α α) (f : Canticle α) (p n e r) : Refrain M f p (n+1) e r =
    (↑(n+1:ℕ):ℝ)⁻¹ • (chirp M p (Refrain M f p n e (r+2)) + (1/2:ℝ) • (∑ b∈Finset.antidiagonal n,∑ a∈Finset.antidiagonal e,
        symphony M (Refrain M f p b.1 a.1) (Refrain M f p b.2 a.2) r)) := by
  nth_rw 1 [Refrain]; congr 3; exact Finset.sum_coe_sort (Rsum n) (fun b => ∑ a∈Finset.antidiagonal e,symphony M (Refrain M f p b.1 a.1) (Refrain M f p b.2 a.2) r)

def Played (e r : ℕ) := 0<e ∧ ∃ q : ℕ, e+2=r+2*q
def Decked (F : Canticle α) := ∀ e r,F e r≠0 → Played e r
def Treble (n e r : ℕ) := Played e r ∧ 2*n+r ≤ 3*e

variable {p : Option Side} {F : Canticle α}
variable [Fintype α]
lemma chirp_tunable (p) (h : Whole M) {f : Shale α (r+2)} (hf : Summable f) : Tunable (chirp M p f) := (score_tunable (rumba_summable p hf h)).scale _
lemma prolong_tunable (n : ℕ) {F : Shale α r} (h : Tunable F) : Tunable (prolong n F) := by
  by_cases hh : r=n
  · subst n; rw [prolong_self]; exact h
  rw [prolong,dif_neg hh]; exact Tunable.zero ..
lemma symphony_tunable (h : Whole M) {V W : Verse α} (hf : ∀ i, Summable (V i)) (hv : ∀ i,Summable (W i)) : Tunable (symphony M V W r) :=
  Tunable.sum _ fun _ _=> prolong_tunable _ (medley_tunable h (hf _) (hv _))
lemma refrains_tune (h : Whole M) (v : ∀ e r,Tunable (F e r)) (p n e r) : Tunable (Refrain M F p n e r) := by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero => rw [Refrain]; exact v e r
  | ind n ih =>
    rw [Refrain_step]; apply Tunable.scale; apply Tunable.add (chirp_tunable _ h (ih n le_rfl e _).1)
    apply Tunable.scale; refine Tunable.sum _ fun i hi=>Tunable.sum _ (fun a ha => ?_)
    have hp := mem_antidiagonal.mp hi
    exact symphony_tunable h (fun u => (ih i.1 (by omega) a.1 u).1) (fun u => (ih i.2 (by omega) a.2 u).1)
lemma treble_reel (h : Whole M) (v : ∀ e r,Tunable (F e r)) (hv : Decked F) :
    Refrain M F p n e r ≠ 0 → Treble n e r := by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero => rw [Refrain]; intro hp; obtain ⟨he,b,hb⟩ := hv e r hp; exact ⟨⟨he,b,hb⟩,by omega⟩
  | ind n ih =>
    rw [Refrain_step]; contrapose
    intro hp
    have hc : Refrain M F p n e (r+2)=0 := not_ne_iff.mp (mt (ih n le_rfl) (fun ⟨⟨he,j,hj⟩,hu⟩ => hp ⟨⟨he,j+1,by omega⟩,by omega⟩))
    rw [hc,chirp_empty M p h, sum_eq_zero,smul_zero,zero_add,smul_zero]
    intro b hb; apply sum_eq_zero; intro a ha; apply sum_eq_zero
    intro d hd
    have he := mem_antidiagonal.mp ha; have ht := mem_antidiagonal.mp hb; have hx := mem_antidiagonal.mp hd
    by_cases hy : Refrain M F p b.1 a.1 (d.1+1)=0
    · rw [hy,medley_start h (refrains_tune h v p b.2 a.2 _).1,prolong_zero]
    have hy' : Refrain M F p b.2 a.2 (d.2+1)=0 := by
      by_contra hw
      obtain ⟨⟨hk,l,hl⟩,hu⟩ := ih _ (by omega : b.1 ≤ n) hy; obtain ⟨⟨hL,m,hM⟩,hU⟩ := ih _ (by omega : b.2≤n) hw
      exact hp ⟨⟨by omega, l+m,by omega⟩,by omega⟩
    rw [hy',medley_end h (refrains_tune h v p b.1 a.1 _).1,prolong_zero]

def terrace (e : ℕ) := 3*e

def upswell (M : Row α α) (F : Canticle α) (p : Option Side) (t : ℝ) (e r : ℕ) : Shale α r :=
    ∑ a∈ Finset.range (terrace e+1), t^a • Refrain M F p a e r
theorem upswell_deck (M : Row α α) (h : Whole M) (F : Canticle α) (hp : ∀ e r,Tunable (F e r)) (hv : Decked F) (p t) :
    Decked (upswell M F p t) ∧ ∀ e r,Tunable (upswell M F p t e r) := by
  refine ⟨fun e r he=> by_contra (fun ht=> he ?_),fun e r=>Tunable.sum _ fun i _=> (refrains_tune h hp p i e r).scale _⟩
  exact sum_eq_zero fun i _=> by rw [not_ne_iff.mp (mt (treble_reel h hp hv (n:=i) (p:=p) (r:=r)) (fun H=> ht H.1)),smul_zero]
end YM.RG08
