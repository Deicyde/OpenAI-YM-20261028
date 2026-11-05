import YM.RG08.Wallet.Bureau

/-! # Booking uniform grants; inter- & intra-lines

spend FIXED multiples in width before choosing L. Gains/differences may
include scalars from y (small knots), record cutoff rate in δ.
No period or order of actual measure expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {I : Type} {α : I → Type} [∀ i,Fintype (α i)]
variable {y δ δ' δ'' w v u : I → ℝ} {r s : ℕ}
variable {K P : ∀ i,Shale (α i) (r+1)} {M N : ∀ i,Shale (α i) (s+1)}
variable {F T : ∀ i,Shale (α i) (r+2)} {A B : ∀ i, Row (α i) (α i)}
private lemma chips (p : I → Option Side) (hp : 0 ≤ w) (hv : 0≤v)
    (hk : Voucher y δ F ((r+1:ℕ) • w)) (he : SafeRow y δ' A v) (hh : 0≤δ') :
    Voucher y (δ*δ') (fun i=> chirp (A i) (p i) (F i)) w := by
  obtain ⟨x,hx,Hx⟩ := hk; obtain ⟨m,hm,Hm⟩ := he
  refine ⟨_, (Weighed.constant y (norm_nonneg (batting r))).times (hm.times hx), fun i=> ?_⟩
  have hz : Glow (F i) ((↑(r+1 : ℕ):ℝ)*w i) (x i*δ i) := by
    rw [← nsmul_eq_mul]; exact Hx i
  apply glow_less (chirp_price (Hm i) (hv i) hz (hp i) (p i) (mul_nonneg (hm.positive i) (hh i))).1 le_rfl
  exact le_of_eq (by simp only [Pi.mul_apply]; ring)
lemma whisper (p : I → Option Side) (h : Audience y) (hh : 0 ≤ w) (hv : ∀ i,0<v i)
    (ht : Both y δ F T ((r+1:ℕ) • w)) (hk : RowBoth y δ A B v) (hp : 0≤δ) :
    Both y δ (fun i => chirp (A i) (p i) (F i)) (fun i=> chirp (B i) (p i) (T i)) w := by
  have hc : 0 ≤ (1:I→ℝ) := fun _=> zero_le_one
  have hs : 0 ≤ v := fun i=>(hv i).le
  constructor
  · simpa only [mul_one] using chips p hh hs ht.fresh hk.fresh hc
  · simpa only [mul_one] using chips p hh hs ht.again hk.again hc
  have hf i : Summable (F i) := (ht.fresh.choose_spec.2 i).summable (ling_one ((show 0≤(r+1:ℕ) • w from nsmul_nonneg hh _ ) i))
  have ht' i : Summable (T i) := (ht.again.choose_spec.2 i).summable (ling_one ((show 0≤(r+1:ℕ) • w from nsmul_nonneg hh _ ) i))
  let Y i := chirp (A i) (p i) ((F-T) i)
  let V i := chirp ((A-B) i) (p i) (T i)
  rw [show _-_ = Y+V from funext fun i=> by
    change chirp _ _ _ - chirp (B i) _ _=chirp _ _ (F i-T i)+chirp (A i-B i) _ _
    have he := hk.fresh.status hv i; rw [chirp_minus _ (hf _) (ht' _) he, chirp_note _ (ht' _) he (hk.again.status hv i)]; abel]
  exact Voucher.plus (by simpa only [mul_one] using chips p hh hs ht.moves hk.fresh hc)
    (by simpa only [one_mul] using chips p hh hs ht.again hk.moves hp) h

private lemma trills (hw : 0≤w) (hK : Voucher y δ K ((r+s+1:ℕ) • w)) (hM : Voucher y δ' M ((r+s+1:ℕ) • w)) (hp : 0≤δ'') (h : SafeRow y δ'' A (s • ((r+s+1:ℕ) • w))) : Voucher y (δ*δ'*δ'') (fun i=> medley (A i) (K i) (M i)) w := by
  obtain ⟨x,Hx,hx⟩ := hK; obtain ⟨z,Hz,hz⟩ := hM; obtain ⟨t,Ht,ht⟩ := h
  refine ⟨_,(Weighed.constant y (norm_nonneg (syl r s))).times (Ht.times (Hx.times Hz)),fun i=>?_⟩
  have he := ht i; simp only [Pi.smul_apply,nsmul_eq_mul] at he
  have h := hx i; simp only [Pi.smul_apply,nsmul_eq_mul] at h
  have hg:=hz i; simp only [Pi.smul_apply,nsmul_eq_mul] at hg
  exact glow_less (medley_price (hw i) h hg he (mul_nonneg (Ht.positive i) (hp i))).1 le_rfl (le_of_eq (by simp only [Pi.mul_apply]; ring))

lemma charring (h : Audience y) (hp : 0≤w) (ht : Both y δ K P ((r+s+1:ℕ) • w)) (hk : Both y δ M N ((r+s+1:ℕ) • w)) (hv : RowBoth y δ A B v) (hb : s • ((r+s+1:ℕ) • w)≤v)
    (he : ∀ i,0<v i) (hδ : 0≤δ) : Both y δ (fun i=> medley (A i) (K i) (M i)) (fun i=> medley (B i) (P i) (N i)) w := by
  have h1 : 0 ≤ (1:I→ℝ) := fun _=> zero_le_one
  have hQ := hv.fresh.soften hb; have hX := hv.again.soften hb; have hP:= hv.moves.soften hb
  constructor
  · simpa only [mul_one] using trills hp ht.fresh hk.fresh h1 hQ
  · simpa only [mul_one] using trills hp ht.again hk.again h1 hX
  let D i := medley (A i) ((K-P) i) (M i)
  let T i := medley (A i) (P i) ((M-N) i)
  let R i := medley ((A-B) i) (P i) (N i)
  have hc : 0≤ (r+s+1:ℕ) • w := nsmul_nonneg hp _
  rw [show _ - _ = D+T+R from funext fun i=> by
    change medley _ _ _-medley _ _ _=medley _ (K i-P i) _+medley _ _ (M i-N i)+medley (A i-B i) _ _
    have hf i := (ht.fresh.choose_spec.2 i).summable (ling_one (hc i))
    have hg i := (ht.again.choose_spec.2 i).summable (ling_one (hc i))
    have hl i := hv.fresh.status he i
    have hs i := (hk.fresh.choose_spec.2 i).summable (ling_one (hc i))
    have HX i := (hk.again.choose_spec.2 i).summable (ling_one (hc i))
    rw [medley_single (hl i) (hf i) (hg i) (hs i), medley_dual (hl i) (hg i) (hs i) (HX i), medley_flow (hl i) (hv.again.status he i) (hg i) (HX i)]; abel]
  apply Voucher.plus _ _ h
  exacts [Voucher.plus (by simpa only [mul_one] using trills hp ht.moves hk.fresh h1 hQ) (by simpa only [one_mul,mul_one] using trills hp ht.again hk.moves h1 hQ) h, by simpa only [one_mul] using trills hp ht.again hk.again hδ hP]
end YM.RG08
