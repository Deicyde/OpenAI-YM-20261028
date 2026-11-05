import YM.RG08.Wallet.Exchange

/-!
# Acyclic predecessor masses

Multipliers known before lengths. Per-family constants in hypotheses
fixed once. Don’t extract a repeated width from a gap `at this L`.
At time successor, predecessor inputs strictly earlier in the partial order,
within grade ONLY at LARGER initial field ranks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {I : Type} {α : I → Type} [∀ i,Fintype (α i)]
variable {Q U : ∀ i, Row (α i) (α i)} {F H : ∀ i, Canticle (α i)}
variable {p : I → Option Side} {n r m k e i j s D : ℕ} {y δ w v : I→ℝ}

def funding (u t : ℕ) := (u+4)^(2*t+1)
def RootStep (n e r i j : ℕ) := Played i j ∧ (i < e ∨ (i=e ∧ if n=0 then r≤ j else r<j))

private lemma funding_succ (h : m≤n) (hr : s ≤ e+4) : funding e m*s≤funding e (n+1) := by
  unfold funding; calc
    _ ≤ (e+4)^(2*n+1)*(e+4) := by gcongr; omega
    _ = (e+4)^(2*n+1+1) := by ring
    _ ≤ _ := by gcongr <;> omega
private lemma money_succ (hk : k≤e) (h : m≤n) (hr : s ≤ e+4) : funding k m*s≤funding e (n+1) :=
    le_trans (show funding k m*s≤ funding e m*s from Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : k+4 ≤ e+4) _)) (funding_succ h hr)
private lemma paid_w_r (hv : 0 ≤ w) (hq : funding e (n+1) • w ≤ v) (ha : r≤e+2) (hh : m ≤ n) (hk : k ≤ e) :
    funding k m • ((r+1) • w) ≤ v := by rw [← mul_smul]; exact le_trans (by gcongr; exact money_succ hk hh (by omega)) hq
private lemma rank_less (ha : Treble n e r) : r ≤ e+2 := by obtain ⟨⟨h,q,hq⟩,hp⟩ := ha; omega

-- spelling varies alphabet; same choice p; NO counts from cardinality here
theorem crypt (h : Audience y) (hh : 0≤δ) (hw : 0 ≤ w) (hp : ∀ i,0<v i) (hq : RowBoth y δ Q U v)
    (ht : ∀ i, Decked (F i) ∧ ∀ e r,Tunable (F i e r)) (hg : ∀ i, Decked (H i) ∧ ∀ e r,Tunable (H i e r))
    (p : I → Option Side) (hz : funding e n • w ≤ v) (hx : ∀ i j, RootStep n e r i j →
        Both y δ (fun b => F b i j) (fun b=> H b i j) v) :
    Both y δ (fun b => Refrain (Q b) (F b) (p b) n e r) (fun b => Refrain (U b) (H b) (p b) n e r) w := by
  have h1 i:=hq.fresh.status hp i; have h2 i:=hq.again.status hp i
  let V i := Refrain (Q i) (F i) (p i)
  let W i := Refrain (U i) (H i) (p i)
  have hv1 i n e r := refrains_tune (h1 i) (ht i).2 (p i) n e r
  have hv2 i n e r := refrains_tune (h2 i) (hg i).2 (p i) n e r
  have hz1 (i) {n e r : ℕ} (h : ¬ Treble n e r) : V i n e r=0 := not_ne_iff.mp (mt (treble_reel (h1 i) (ht i).2 (ht i).1) h)
  have hz2 (i) {n e r : ℕ} (h : ¬ Treble n e r) : W i n e r=0 := not_ne_iff.mp (mt (treble_reel (h2 i) (hg i).2 (hg i).1) h)
  change Both y δ (fun i=> V i _ _ _) (fun i=> W i _ _ _) _
  induction n using Nat.caseStrongRecOn generalizing e r w with
  | zero =>
    by_cases hv : Treble 0 e r
    · simp only [V,W,Refrain]
      apply (hx e r ⟨hv.1,Or.inr ⟨rfl,by simp⟩⟩).soften
      refine le_trans ?_ hz
      have hh : 1 ≤ funding e 0 := by unfold funding; simp
      simpa only [one_smul] using smul_le_smul_of_nonneg_right hh hw
    rw [show (fun i=> V i 0 e r)=0 from funext fun i=> hz1 i hv,show (fun i=> W i 0 e r)=0 from funext fun i => hz2 i hv]; exact Both.zero
  | ind n IH =>
    by_cases hu : Treble (n+1) e r
    swap
    · rw [show (fun i=> V i _ _ _)=0 from funext fun i=> hz1 i hu,show (fun i=> W i _ _ _)=0 from funext fun i=> hz2 i hu]; exact Both.zero
    have hr := rank_less hu
    let μ := (r+1 : ℕ) • w
    have hμ : 0 ≤ μ := nsmul_nonneg hw _
    have hy : ∀ i j, RootStep n e (r+2) i j → RootStep (n+1) e r i j := fun i j ha => ⟨ha.1,ha.2.imp_right fun hw=>⟨hw.1,by rw [if_neg (by omega)]; obtain ⟨_,hx⟩:= hw; split at hx <;> omega ⟩⟩
    have hC := whisper p h hw hp (F:=fun i=> V i n e (r+2)) (T:=fun i=> W i n e (r+2)) (IH n le_rfl hμ (paid_w_r hw hz hr le_rfl le_rfl) fun i j hj=> hx i j (hy i j hj)) hq hh
    let R (b a : ℕ×ℕ) i := symphony (Q i) (V i b.1 a.1) (V i b.2 a.2) r
    let T (b a : ℕ×ℕ) i := symphony (U i) (W i b.1 a.1) (W i b.2 a.2) r
    have hb (b a : ℕ×ℕ) (ht : b∈wheel n) (ha : a∈wheel e) : Both y δ (R b a) (T b a) w := by
      have he := mem_antidiagonal.mp ht; have hy := mem_antidiagonal.mp ha
      apply Both.list (wheel r) h (F:=fun j i=> prolong r (medley (Q i) (V i b.1 a.1 (j.1+1)) (V i b.2 a.2 (j.2+1)))) (H:=fun j i=> prolong r (medley (U i) (W i b.1 a.1 (j.1+1)) (W i b.2 a.2 (j.2+1))))
      intro t ht
      have hY := mem_antidiagonal.mp ht
      by_cases hJ : Treble b.1 a.1 (t.1+1); swap
      · simp only [hz1 _ hJ,hz2 _ hJ,V,W,medley_start (h1 _) (hv1 .. |>.1),medley_start (h2 _) ((hv2 ..).1),prolong_zero]; exact Both.zero
      by_cases hE : Treble b.2 a.2 (t.2+1); swap
      · simp only [hz1 _ hE,hz2 _ hE,V,W,medley_end (h1 _) (hv1 ..|>.1),medley_end (h2 _) ((hv2 ..).1),prolong_zero]; exact Both.zero
      have hc (a m k) (h : m ≤ n) (ht : a < e) : Both y δ (fun i=>V i m a k) (fun i=> W i m a k) μ := by
        apply IH m h hμ (paid_w_r hw hz hr h ht.le)
        intro u v hv; exact hx u v ⟨hv.1, Or.inl (lt_of_le_of_lt (hv.2.elim Nat.le_of_lt (fun H=> H.1.le)) ht)⟩
      have hP := (charring (K:=fun i=> V i b.1 a.1 (t.1+1)) (M:=fun i=> V i b.2 a.2 (t.2+1)) h hw
        (r:=t.1) (s:=t.2) (by rw [hY]; exact hc a.1 b.1 _ (by omega) (by have hh := hE.1.1; omega))
        (by rw [hY]; exact hc a.2 b.2 _ (by omega) (by have hh:= hJ.1.1; omega)) hq ?_ hp hh)
      · subst r; simp_rw [prolong_self]; exact hP
      rw [← mul_smul,hY]
      refine le_trans ?_ hz; apply smul_le_smul_of_nonneg_right _ hw
      unfold funding
      calc
        _ ≤ (e+4)*(e+4) := Nat.mul_le_mul (by omega) (by omega)
        _ = (e+4)^2 := by ring
        _ ≤ _ := by gcongr <;> omega
    let l i := ∑ b∈wheel n,∑ a∈wheel e,R b a i; let l' i:= ∑ b∈wheel n,∑ a∈wheel e,T b a i
    have hs : Both y δ l l' w := Both.list _ h (fun b hx => Both.list _ h (fun a ha=> hb b a hx ha))
    unfold V W; simp_rw [Refrain_step]; exact (hC.add (hs.weight (1/2)) h).weight _
end YM.RG08
