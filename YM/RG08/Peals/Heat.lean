import YM.RG08.Peals.Rain

/-! # The inherited energy batches solve the connected-log heat equation

Specific literal recursions from Wilson cover stencils. Unconditional slices
of heat charge. (For one mark solve a different transport.) -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff
variable {α X ι : Type}
variable {M : Row α α} {e n J D : ℕ} {m : Side} {F : Canticle α} {K : Verse α}
variable [Fintype α] [DecidableEq α]

private def Past (K : Verse α) (n : ℕ) := ∀ i : ℕ,n < i → K i=0
omit [Fintype α] [DecidableEq α] in
private lemma tally (he : Played e J) : J ≤ e+2 := by obtain ⟨_,q,hq⟩ := he; omega
omit [DecidableEq α] in
private lemma grand_past (h : Past K J) (hp : J ≤ D) (m) : grand D K m=grand J K m := by
  unfold grand; symm; apply sum_subset (range_mono (by omega)); intro i hi he; rw [h i (by simp only [mem_range,not_lt] at he; omega),stanza_zero]
omit [DecidableEq α] in
private lemma ripe (h : Whole M) (v : ∀ i j,Tunable (F i j)) (hf : Decked F) (p n e) : Past (Refrain M F p n e) (e+2) := by
  intro i hi; exact not_ne_iff.mp (mt (treble_reel h v hf) (fun H=> (Nat.not_lt.mpr (tally H.1)) hi))

-- smooth functions product B-space, not polynomials themselves
abbrev Scroll (R : Type) := ℕ → ℕ → R

def Beats (M : Row α α) (F : Canticle α) (m : Side) : Scroll (Psalm (Co m α)) :=
    fun n e=> grand (e+2) (Refrain M F (some m) n e) m

def Fluid [Fintype X] (F : Scroll (Psalm X)) := ∀ n e, ContDiff ℝ ω (F n e)
def tempered (R : Type) [Zero R] (F : Scroll R) := ∀ n e, terrace e < n → F n e=0
def Muted (R : Type) [Zero R] (F : Scroll R) := ∀ n, F n 0=0
def Views [Fintype X] [DecidableEq X] (M : Matrix X X ℝ) (F : Scroll (Psalm X)) := ∀ n e,
    (↑(n+1 : ℕ):ℝ) • F (n+1) e= lap M (F n e) + (1/2:ℝ) • ∑ b∈wheel n,∑ a∈wheel e, arch M (F b.1 a.1) (F b.2 a.2)

omit [DecidableEq α] in
private lemma swell_col (h : Whole M) (v : ∀ i j,Tunable (F i j)) (e m R) (t : ℝ) :
    grand R (upswell M F (some m) t e) m = ∑ b∈range (terrace e+1), t^b • grand R (Refrain M F (some m) b e) m := by
  unfold grand upswell
  simp_rw [stanza_sum (ι:=ℕ) _ _ (fun b _=> (Tunable.scale _ (refrains_tune h v _ b _ _)).1) m];
  simp_rw [stanza_scale _ (refrains_tune h v _ _ _ _).1,Finset.smul_sum]; rw [sum_comm]

lemma head_beats (h : Whole M) (v : ∀ i j,Tunable (F i j)) (hp : Decked F) : Fluid (Beats M F m) ∧
    Muted _ (Beats M F m) ∧ tempered _ (Beats M F m) ∧ Views (M.acts m) (Beats M F m) ∧
    (∀ t e, grand (e+2) (upswell M F (some m) t e) m= ∑ b∈range (terrace e+1), t^b • Beats M F m b e) := by
  constructor
  · intro n e
    unfold Beats grand
    let f r := stanza (Refrain M F (.some m) n e r) m
    rw [show (∑ i∈range (e+2+1),f i)=_ from (funext fun x=> Finset.sum_apply x .. : (∑ i∈range (e+2+1),f i)=(fun x=> ∑ i∈range (e+2+1),f i x))]; exact ContDiff.sum fun i hi=> stanza_smooth ..
  have hu (n e r) : Tunable (Refrain M F (some m) n e r) := refrains_tune h v _ _ _ _
  let S (n e) := (Refrain M F (some m) n e)
  have hx (n e r) : S n e r ≠ 0 → Treble n e r := treble_reel h v hp
  refine ⟨fun i => ?_, fun n e he=>?_,fun n e=>?_,fun t e=> swell_col h v e m (e+2) t⟩
  · unfold Beats grand; apply sum_eq_zero; intro j _; change stanza (S i 0 j) m=_; rw [not_ne_iff.mp (mt (hx i 0 j) fun H=> (Nat.lt_irrefl _ H.1.1).elim)] -- mismatch
    exact stanza_zero _
  · unfold Beats grand; apply sum_eq_zero; intro j _;
    have hr : Refrain M F (.some m) n e j=0 := not_ne_iff.mp (mt (hx n e j) (fun H=> by unfold terrace at he; have hh:= H.2; omega))
    rw [hr, stanza_zero]
  unfold Beats grand
  rw [Finset.smul_sum]
  have Hn : 0<((↑(n+1:ℕ)):ℝ) := by positivity
  let W b a (r : ℕ) := symphony M (S (b : ℕ×ℕ).1 (a : ℕ×ℕ).1) (S b.2 a.2) r
  have he (r) : (↑(n+1:ℕ):ℝ) • stanza (Refrain M F (.some m) (n+1) e r) m=
      stanza (chirp M (some m) (S n e (r+2))) m+ (1/2:ℝ) • (∑ b∈wheel n, ∑ a∈wheel e, stanza (W b a r) m) := by
    have hk (b a) : Tunable (W b a r) := symphony_tunable h (fun _=>(hu _ _ _).1) (fun _=>(hu _ _ _).1)
    have hh (b) : Summable (∑ a∈wheel e,W b a r) := shale_total_sum _ (fun a _=> (hk b a).1)
    have ht := shale_total_sum (wheel n) (fun i _=> hh i)
    have hc : Summable ((1/2:ℝ) • ∑ b∈wheel n,∑ a∈wheel e,W b a r) := ht.mul_left _
    have hy := (chirp_tunable (some m) h (hu n e (r+2)).1).1
    rw [Refrain_step]; change _ • stanza ((↑(n+1:ℕ):ℝ)⁻¹ • (chirp M (some m) (Refrain M F (some m) n e (r+2))+ (1/2:ℝ) • ∑ b∈wheel n, ∑ a∈wheel e,W b a r)) m=_
    rw [stanza_scale _ (show Summable (_ + _) from hy.add hc), smul_inv_smul₀ Hn.ne', stanza_add hy hc, stanza_scale _ ht];
    rw [stanza_sum _ _ (fun i _=> hh i)]; simp_rw [stanza_sum _ _ (fun i _=> (hk _ i).1)]; rfl
  change (∑ r∈range _, ((↑(n+1:ℕ)):ℝ) • stanza (Refrain _ _ _ _ _ _) m) = lap _ (grand (e+2) _ m) + (1/2:ℝ) • _
  simp_rw [he,sum_add_distrib, ← Finset.smul_sum]
  congr 1
  · rw [gran_lap h (hu n e)]; symm
    apply (grand_past (K:=fun r=>chirp M (some m) (S n e (r+2))) (J:=e) _ (by omega : e ≤ e+2) m).symm
    intro i hi
    simp only [show S n e (i+2)=0 from ripe h v hp (.some m) n e _ (by omega),chirp_empty _ _ h]
  congr 1; rw [sum_comm]; apply sum_congr rfl; intro b hb; rw [sum_comm]; apply sum_congr rfl; intro a ha
  have hm := mem_antidiagonal.mp ha
  have hz := repeat_gran_arch (m:=m) (L:=a.1+1) (n:=a.2+1) h (hu b.1 a.1) (hu b.2 a.2) (ripe h v hp (.some m) b.1 a.1) (ripe h v hp (.some m) b.2 a.2)
  rw [show a.1+1+(a.2+1)=e+2 by omega] at hz; exact hz.symm
end YM.RG08
