import YM.RG08.Wallet.Furl

/-! # Ribbon motion in qualitative and uniform earns -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff Classical
variable {r : ℕ}
section guaranteed
variable {α β : Type} [Fintype α] [Fintype β]
variable {U V : Shale α r} {A : Row α β} {m : Side} {X : ℕ→Shale α r}

def scrollL (U : Shale α r) (A : Row α β) := score (RG08.ribbon U (fun _=>A))
omit [Fintype α] in
lemma scroll_price (K : Row α β) {w B C : ℝ} (h : Glow U ((r+1:ℕ)*w) B) (hw : 0≤w) (hh : 0≤C)
    (he : K.strip ((r+1:ℕ)*w) C) : Glow (scrollL U K) w (((Fintype.card β:ℝ)^r*C^r)*B) := by
  apply score_price _ hw
  simpa only [prod_const,card_univ,Fintype.card_fin] using ribbon_price U (fun i=>K) h (by positivity) (fun _=>hh) (fun i=>he)
omit [Fintype α] in
lemma scroll_tune (h : Summable U) (ht : Whole A) : Tunable (scrollL U A) := score_tunable (ribbons_sum h (fun _=> ht))
lemma scroll_play (h : Summable U) (ht : Whole A) (x : PAC β m) : stanza (scrollL U A) m x= stanza U m (A.acts m *ᵥ x) := by
  unfold scrollL; rw [stanza_score (ribbons_sum h (fun _=>ht))]; exact ribbon_eval_all h (fun _=>ht) _ _
omit [Fintype α] in
lemma scroll_less (h : Summable U) (p : Summable V) (ht : Whole A) : scrollL (U-V) A=scrollL U A-scrollL V A := by
  unfold scrollL; rw [ribbon_less h p (fun _=>ht),score_sub (ribbons_sum h (fun _=>ht)) (ribbons_sum p (fun _=>ht))]
omit [Fintype α] in
lemma scroll_more (h : Summable U) (p : Summable V) (ht : Whole A) : scrollL (U+V) A=scrollL U A+scrollL V A := by
  have hf : Summable (U+V) := h.add p; have he := scroll_less hf p ht; rw [add_sub_cancel_right] at he
  exact eq_add_of_sub_eq he.symm
omit [Fintype α] in
lemma nobody (p : ℕ) (h : Whole A) : scrollL (0:Shale α p) A=0 := by
  have hp : Summable (0:Shale α p) := summable_zero; simpa only [sub_self] using scroll_less hp hp h
omit [Fintype α] in
private lemma loan {M : ℝ} {α β : Type} {A : Row α β} (h : Whole A) (hv : 0<M) (n : ℕ) :
    ∃ w B : ℝ, 0<w ∧ 0 ≤ B ∧ (↑(n+1:ℕ):ℝ)*w≤M ∧ A.strip ((n+1:ℕ)*w) B := by
  obtain ⟨s,C,hs,H⟩:=h
  let t:=min M s
  have he : 0<t := lt_min hv hs
  have ht : 0<((↑(n+1:ℕ)):ℝ) := by positivity
  refine ⟨t/(↑(n+1:ℕ):ℝ),max C 0,div_pos he ht,le_max_right ..,by rw [mul_div_cancel₀ t ht.ne']; exact min_le_left ..,Work.F08.strip_mono H ?_ (le_max_left ..)⟩
  rw [mul_div_cancel₀ t ht.ne']; exact min_le_right ..
omit [Fintype α] in
lemma scroll_adm (h : Glows U) (ht : Whole A) : Glows (scrollL U A) := by
  obtain ⟨w,C,hp,H⟩:=h; obtain ⟨b,D,hb,hD,hU,hV⟩ := loan ht hp r
  exact ⟨_,_,hb,scroll_price _ (glow_less H hU le_rfl) hb.le hD hV⟩
omit [Fintype α] in
lemma scroll_thread (h : Mending X U) (ht : Whole A) : Mending (fun i=> scrollL (X i) A) (scrollL U A) := by
  have hf i := (Mending.ever h i).summable
  have hh := h.1.summable
  have he i : scrollL (X i) A-scrollL U A=scrollL (X i-U) A := (scroll_less (hf i) hh ht).symm
  refine ⟨scroll_adm h.1 ht,?_⟩
  simp only [he]; obtain ⟨b,δ,hb,hδ,H⟩:=h.2
  obtain ⟨w,B,hw,hp,hS,hH⟩:= loan ht hb r
  let z:= (Fintype.card β:ℝ)^r*B^r
  exact ⟨_,fun i=> z*δ i,hw,by simpa using hδ.const_mul z,fun i=> scroll_price _ (glow_less (H i) hS le_rfl) hw.le hp hH⟩
end guaranteed

section variation
variable {I J : Type} {α β : I→Type} [∀ i,Fintype (α i)] [∀ i,Fintype (β i)] {y v w δ : I→ℝ} {x : I→Side}
variable {V T : ∀ i,Shale (α i) r} {C B : ∀ i,Row (α i) (β i)}
omit [∀ i,Fintype (α i)] in
lemma Voucher.score (h : 0≤w) (hp : Voucher y δ V ((r+1:ℕ) • w)) : Voucher y δ (fun i=> RG08.score (V i)) w := by
  refine ⟨_,hp.choose_spec.1,fun i=> ?_⟩; have hh := hp.choose_spec.2 i; simp only [Pi.smul_apply,nsmul_eq_mul] at hh; exact score_price hh (h i)
omit [∀ i, Fintype (α i)] in
lemma remit (h : ∀ i, 0<w i) (hg : Audience y) (hδ : 0 ≤ δ) (hv : Both y δ V T ((r+1:ℕ) • w))
    (hf : RowBoth y δ C B ((r+1:ℕ) • w)) (hp : Weighed y (fun i=> (Fintype.card (β i):ℝ))) :
    Both y δ (fun i=>scrollL (V i) (C i)) (fun i=>scrollL (T i) (B i)) w := by
  let μ : I→ℝ := (r+1:ℕ) • w
  have he i : 0<μ i := smul_pos (Nat.succ_pos _) (h i)
  have hh : 0 ≤ w := fun i=> (h i).le
  have hx : 0 ≤ μ := fun i=> (he i).le
  have hA := bind_budget hx hv.fresh (A:=fun _=>C) (fun _=> hf.fresh) hp
  have hB := bind_budget hx hv.again (A:=fun _=>B) (fun _=> hf.again) hp
  constructor
  · exact Voucher.score hh hA
  · exact Voucher.score hh hB
  let X i := RG08.ribbon ((V-T) i) (fun _=>C i)
  let Y i := RG08.ribbon (T i) (fun _=> C i)-RG08.ribbon (T i) (fun _=> B i)
  let Z i := RG08.ribbon (V i) (fun _=> C i)-RG08.ribbon (T i) (fun _=> B i)
  have ht i : Summable (T i) := (hv.again.choose_spec.2 i).summable (ling_one (hx i))
  have hV i : Summable (V i) := (hv.fresh.choose_spec.2 i).summable (ling_one (hx i))
  have hc i := hf.fresh.status he i
  have hm i := hf.again.status he i
  rw [show _-_ = (fun i=>score (Z i)) from funext fun i => by
    unfold Z; rw [score_sub (ribbons_sum (hV i) (fun _=>hc i)) (ribbons_sum (ht i) (fun _=>hm i))]; rfl]
  apply Voucher.score hh
  have hX : X+Y=Z := by ext1 i; unfold X Y Z; rw [Pi.add_apply,Pi.sub_apply (g:=T), ribbon_less (hV _) (ht _) (fun _=>hc _)]; abel
  rw [← hX]
  exact (bind_budget hx hv.moves (A:=fun _=>C) (fun _=>hf.fresh) hp).plus (exchangeR he hg hδ hv.again (fun _=>hf) hp) hg
end variation
end YM.RG08
