import YM.RG12.Shadows.Fare
/-! Currency on Uniform real scalar germs ONLY at 0. Polar transfers k unbounded in history
but test capped to n.C. Changing order loses pressure. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Function Filter ConnectedActivityE6 ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{n:ℕ}{p t :ℝ}{I I' J:ℕ→Type}{E:ℕ→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] {b:∀ i,E i}
abbrev Drift (I E:ℕ→Type):= (i:ℕ)→I i→E i→ℝ
def Call (R:Haze)(n:ℕ)(p:ℝ)(f:Drift I E) := ∃ w, Charges R p w ∧ ∀ᶠ i:ℕ in atTop,∀ j:I i,Brush n (w i) 1 (f i j) 0
namespace Call
variable {f g:Drift I E}(h:Call R n p f){Z:ℕ→ℝ}
include h
lemma mono (hp:t≤p):Call R n t f:=by obtain ⟨w,hz,hh⟩:=h; exact ⟨_,hz.slower hp,hh⟩
lemma nonneg :∃ w, Charges R p w ∧ (∀ i,0 ≤ w i) ∧ ∀ᶠ i:ℕ in atTop,∀ j:I i,Brush n (w i) 1 (f i j) 0:=by
   obtain ⟨w,hz,hh⟩:=h; exact ⟨_, hz.absolute,fun _=>abs_nonneg _,hh.mono fun i ha j=> (ha j).climb (le_abs_self _) le_rfl⟩
lemma reindex (r:∀ i,I' i→ I i): Call R n p (fun i k=> f i (r i k)):=by obtain ⟨_,ha,hb⟩:=h; exact ⟨_,ha,hb.mono fun i hi j=> hi _⟩
lemma fakes (hg:∀ᶠ i:ℕ in atTop,∀ j, g i j =ᶠ[𝓝 0] f i j):Call R n p g:=by obtain ⟨_,ha,hb⟩:=h; exact ⟨_,ha,(hb.and hg).mono fun i hi j=> (hi.1 j).shimmy (hi.2 j)⟩
lemma same (hg:∀ i j x, g i j x=f i j x):Call R n p g:=h.fakes (Eventually.of_forall (fun i j=> Eventually.of_forall (hg i j)))
omit h in
lemma flat {f:∀ i:ℕ,I i→ℝ}(hK: Keeps R p I f) : Call (E:=E) R n p (fun i j _=> f i j):=by -- unused y use _
   obtain ⟨v,ha,hb⟩:=hK; exact ⟨_,ha,hb.mono fun i hi j=> (Brush.certified (x:=(0:E i)) zero_le_one _).climb (hi j) le_rfl⟩
omit h in
lemma up {f:ℕ→ℝ}(hK: Charges R p f): Call (I:=I) (E:=E) R n p (fun i _ _=> f i):= flat ⟨_,hK.absolute,Eventually.of_forall fun _ _=> le_rfl⟩
omit h in
lemma warmed (r:ℝ): Call (I:=I) (E:=E) R n 0 (fun _ _ _=> r):= up (Charges.frozen r R)
-- Trim of product (adds constant)
lemma adds (hg: Call R n p g):Call R n p (f+g):=by
   obtain ⟨v,ha,hf⟩:=h; obtain ⟨w,hb,hg⟩:=hg; exact ⟨_,ha.add hb,(hf.and hg).mono fun i hi j=> ((hi.1 j).gathering (hi.2 j))⟩
lemma times (hg:Call R n t g):Call R n (p+t) (f*g):=by
   obtain ⟨v,ha,hf⟩:=h; obtain ⟨w,hb,hg⟩:=hg; exact ⟨_,(ha.mul hb).right ((1+(1+1))^n),(hf.and hg).mono fun i hi j=> ((hi.1 j).paints (hi.2 j)).trim⟩
lemma coat (a:ℝ):Call R n p (a • f):=by obtain ⟨_,ha,hf⟩:=h; exact ⟨_,ha.left ‖a‖,hf.mono fun i hi j=> (hi j).smul _⟩
lemma negates:Call R n p (-f):=by obtain ⟨v,ha,hf⟩:=h; exact ⟨_,ha,hf.mono fun i hi j=> (hi j).opposite⟩
lemma subs (hg: Call R n p g):Call R n p (f-g):=by simpa only [sub_eq_add_neg] using h.adds hg.negates
lemma totals [∀ i,Fintype (J i)] (r:∀ i,I' i→J i→I i)(hv:Charges R t (fun i=> (Fintype.card (J i):ℝ))) : Call R n (t+p) (fun i k x=>∑ j:J i,f i (r i k j) x):=by
   obtain ⟨v,ha,hb⟩:=h; exact ⟨_,hv.mul ha,hb.mono fun i hi k=>by
      have hh:=Brush.spree Finset.univ (fun j : J i=> f i (r i k j)) (fun _=>v i) zero_le_one (fun j _=> hi _); simpa only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul] using hh⟩
local notation "opp" => (-1:ℝ) -- for y mirrors
lemma flips : Call R n p (fun i j y=> f i j (-y)):=by
  obtain ⟨_,ha,hb⟩:=h; refine ⟨_,ha,hb.mono fun i hi j=>?_⟩
  let L:= -(ContinuousLinearMap.id ℝ (E i)); have hL:‖L‖≤1:= by simpa only [L,norm_neg] using ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=E i)
  have h0: L 0=0:=map_zero _
  have hu := Brush.reading L (x:=0) (show Brush n _ 1 (f i j) (L 0) from h0.symm ▸ hi j) hL; rw [one_mul] at hu; apply hu.shimmy
  exact Eventually.of_forall fun _=>rfl
end Call
end YM.RG12.Shadows
