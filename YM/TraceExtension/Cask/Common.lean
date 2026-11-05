import YM.TraceExtension.Cask.Burst
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {V L W:Type}[DecidableEq V][DecidableEq L][DecidableEq W]{n:Side}[Fintype V][Fintype L][Fintype W]{G:Gauge}{R:Rep G n}(C:TourC R V L W)
local notation "P"=> agency C
local notation "y!"=> R.p.threshold
local notation "N!"=>lance C
local notation "r!"=> R.p.B
private def zipA (i : Axe C) : Ballot C (fun i : BoxF n=> i.val.1) (fun _ _=> True):=⟨i.1,⟨i.2.val,i.2.property,trivial⟩⟩
private lemma zip_inj : Function.Injective (zipA C):=by
    let f(j:Ballot C (fun i:BoxF n=> i.val.1) (fun _ _=>True)):Axe C:=⟨j.1,⟨j.2.val,j.2.property.1⟩⟩; exact Function.LeftInverse.injective (f:=zipA C) (g:=f) (fun i=>rfl)
-- bets δ_K+ κEx.Spare
lemma lay (w:ℝ)(e u b:ℝ) (h:AirC C) {δ:ℝ}(hh:R.activities.Valid R.p δ b) (hp:0 ≤ e)(hk:e+2≤R.p.supportExponent)
    (a k:ℕ)(c:ℝ)(h':1 ≤ c)(ha:1 ≤ a)(hs:∀ i j,i≠j→64*r!*a+2*r!≤ separation (C.tie i) (C.tie j))(ht:(Set.univ:Set V).PairwiseDisjoint C.cap)(hH:∀ i,coverNumber r! (C.cap i)≤ k)(hξ:4*c*Real.exp ((e+1)*(k:ℝ)) ≤ Real.exp a)(hw:1 ≤ w)
    (l r:ℝ)(hl:4*l ≤ 1)(Z:L→ℝ)(hZ:∀ i,0 ≤ Z i∧∀ U,|C.long i U| ≤ Z i)(h₁:Hit C.path r! Z (e+2) l)
    (y:W→ℝ) (hy:∀ i,0≤ y i∧∀ U v,‖C.paint i U v‖* (w^2/c) ≤ y i)(h₂: Hit C.size r! y (e+1) r)
    (hz: let t:=r+(2*4*Real.exp a*l+2*Real.exp a*b); (((r! + r! +1)^4:ℕ):ℝ)*t ≤ 1 ∧ Real.exp t-1 ≤ u) : Decked P R N! (fun _=>w) e u:=by
    have hhx:0 ≤ l:= Planned.GuardedAtom.sumBudget_credit (h₁ 0); have hd:0 ≤ e+1:= by positivity
    obtain ⟨f,hf,H⟩:= florW R hh; have hb:= Planned.GuardedAtom.sumBudget_credit (H 0)
    have hz':2*(2*c)*Real.exp ((e+1)*(k:ℝ)) ≤ Real.exp a:=by linarith only [hξ]
    have ht' : 2 ≤ 4*c*Real.exp ((e+1)*(k:ℝ)):=by
       have hp:= Real.one_le_exp (show 0 ≤ (e+1)*(k:ℝ) by positivity); nlinarith only [hp,h',mul_le_mul h' hp zero_le_one (zero_le_one.trans h')]
    have hc':1 ≤ 2*c:=by linarith only [h']
    have hs':e+1+1=e+2:=by ring
    let h'':Hit C.path r! Z (e+1+1) l:=by rw[hs']; exact h₁
    let g:=orbitP C 4 (2*c) r! C.path Z (fun _ s=> s.Nonempty)
    have hm:Hit (excerpt C ∘ Sum.inr ∘ Sum.inl) r! g (e+1) (2*4*Real.exp a*l):= brush_hit C r! (e+1) hd R.p.B_pos l (2*c) 4 hhx hc' (by norm_num) k C.path Z _ (fun i=>(hZ i).1) h'' a ha ht hH hs hz'
    let K':= fun t:BoxF n=> t.val.1; let g':= orbitP C 1 (2*c) r! K' (f ∘ Subtype.val) (fun _ _=>True); let p':=g' ∘ zipA C
    have hs(s) :0≤ g s:= by unfold g orbitP; exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (hZ _|>.1)
    have hg'(s): 0≤ g' s:=by unfold g' orbitP; exact mul_nonneg (mul_nonneg zero_le_one (by positivity)) (hf _|>.1)
    have hK:Hit K' r! (f ∘ Subtype.val) (e+1+1) b:=fun i=> Extra.Multi.Budget.pull_le (p:=fun _=>True) (H i) (fun i=> by split; exact mul_nonneg (hf _|>.1) (Real.exp_pos _).le; exact le_rfl) (fun _ _=> trivial) Subtype.val_injective.injOn (fun j _=> by
       dsimp only [K',Function.comp_apply]; split; next he=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (hs'.trans_le hk) (by positivity))) ((hf _).1)
       next he=> rfl)
    have hL: Hit (excerpt C ∘ Sum.inr ∘ Sum.inr) r! p' (e+1) (2*Real.exp a*b):=by
       rw [show (2:ℝ)*Real.exp a=2*1*Real.exp a from by ring]; intro i; exact Extra.Multi.Budget.pull_le (p:=fun _=>True) (brush_hit C r! (e+1) hd R.p.B_pos b (2*c) 1 hb hc' zero_le_one k K' (f ∘ Subtype.val) (fun _ _=> True) (fun i=>hf _|>.1) hK a ha ht hH (by assumption) hz' i) (fun i=> by split; exact mul_nonneg (hg' _) (Real.exp_pos _).le; exact le_rfl) (fun _ _=>trivial) (zip_inj C).injOn (fun j _=> by rfl)
    let F: LandC C→ℝ:= Sum.elim y (Sum.elim g p'); have ht:Hit (agency C|>.foot) r! F (e+1) (r+(2*4*Real.exp a*l+2*Real.exp a*b)):= transK _ _ C.size _ y _ r _ h₂ (transK _ _ _ _ _ _ _ _ hm hL)
    have hi (i):0 ≤ F i:= match i with| .inl i=> (hy _).1| .inr (.inl i)=> hs i| .inr (.inr i)=>hg' _
    refine ⟨spoke C h hh, tells C h hh, fun g=>⟨C.adjust g,tense C h hh g⟩, loaded C h hh,fun i U v=> kink C h hh U v i,clasp C h hh,clearcut C h hh, ⟨hp,_, F,hi,ht,hz.1,hz.2,fun s hs' ht hx U v=> ?_⟩⟩
    rw [show Poly.toll _ (spanZ (crew P s))=(w^2)^(crew P s).card from ?_]; swap; · simp only[Poly.toll,spanZ,prod_const,card_product,card_univ,Fintype.card_bool]; rw [mul_comm _ 2, pow_mul]
    have he:1 ≤ w^2:= one_le_pow₀ hw
    refine tollC C (w^2) c s ht (fun i=> ‖lance C i U v‖) F h' he (fun _=>norm_nonneg _) (fun i=> ?_)
    rcases i with i|(i|i)
    · rw [if_pos (show (agency C).shop (.inl i) from rfl)]; exact (hy i).2 _ _
    · rw [if_neg (show ¬ (agency C).shop (.inr (.inl i)) from by simp[agency])]; let j:= deer C (C.path i.1); have hC: 0 ≤ Z i.1:= (hZ _).1
      have hQ : Real.log 2 ≤ a:=by rw [Real.log_le_iff_le_exp (by norm_num)]; exact ht'.trans hξ
      apply (mul_le_mul (loftPay C Z _ _ _ hd hl hQ ha (by assumption) hZ h'' i U v) (show c^i.2.val.card ≤ c^j.card from pow_le_pow_right₀ h' (card_le_card i.2.property.1)) (pow_nonneg (zero_le_one.trans h') _) (show 0 ≤ (4:ℝ)*2^j.card*Z i.1 by positivity)).trans
      change _ ≤ g _; unfold g orbitP; rw [mul_pow]; unfold j; apply le_of_eq; ring
    rw [if_neg (show ¬ (agency C).shop (.inr (.inr i)) from by simp[agency])]; let j:= deer C i.1.val.1; have hQ:0 ≤ f i.1.val:= (hf _).1
    refine (mul_le_mul (rashPay C f hf i U v) (show c^i.2.val.card ≤ c^j.card from pow_le_pow_right₀ h' (card_le_card i.2.property)) (pow_nonneg (zero_le_one.trans h') _) (show 0 ≤ (2:ℝ)^j.card*f i.1.val by positivity)).trans ?_
    change _≤1*(2*c)^j.card*f i.1.val; rw [mul_pow]; apply le_of_eq; ring
end YM.Trace.Cask
