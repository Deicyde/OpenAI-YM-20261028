import YM.UVExtension.Concert.Antler
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Filter Set RG Wilson Lattice Pressure Push Push.AbsoluteSums Finset Lamppost Progress.DirectedRecipe Payments
open PhysicalNext.Repeat Marlin Ovens.Pipes AnalyticBridge VerifiedReset Extra.Iteration MeasureTheory
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {n:Side} {X:Ovens.Pipes G n} {q p:BudgetPoint} {κ γ w a b: ℝ} {D Z:Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {M:Opening D Z}
-- Raw standing. Supports not claiming indices inherited by Buy; Keeps orientation
-- promotes one seed reward.
variable (Y:D→ Ovens.Tap G n) (F: ℕ≃ X.Pellet)
def softer (X:Ovens.Pipes G n) (b:ℕ) (s:ℝ):Meter ℕ (Site n) where
    test _:= Config G n
    cost x i:= if x∈ X.softer i then Real.exp (s*coverNumber b (X.softer i)) else 0
    nonneg i j:= by split <;> positivity
    awake i:= by obtain ⟨x,hx⟩:= X.sites i; exact ⟨x,by rw [if_pos hx]; exact Real.exp_pos _⟩
lemma soot (X:Ovens.Pipes G n) (b:ℕ) (s:ℝ)(f:ℕ→ℝ)(d:ℝ) : (∀ i,SumBudget (fun j=> (softer X b s).cost i j*f j) d) ↔ Ac.Hit X.softer b f s d:=by
  unfold softer Ac.Hit; simp only [ite_mul,zero_mul]; simp only [mul_comm]

variable (h:Atlas (bell X.kernel p.B (p.supportExponent+1)) M (fun i j (u:Config G n)=> (Y i).forced j u) (fun _=>a)) (H:Atlas (softer X p.B (p.supportExponent+1)) M (fun i j u=> (Y i).logarithm j u) (fun _=>b))
def rind (u:Config G n)(l:Ovens.Label)(z:Z):= l.elim (fun i=>h.f z i u) (fun i=>Complex.exp (H.f z i u)-1)
-- Numbering can depend on geometry. Inspect after connecting readdress.
def bitter (q:BudgetPoint) (u:Config G n) (i:ℕ) (z:Z): ℂ:= if (addr F q i).eligible q.threshold u then ∏ l∈(F i).val,rind Y h H u l z else 0
lemma bitterS (u:Config G n)(i:ℕ)(Z:D): bitter Y F h H p u i (M.call Z)=↑(solid F p (Y Z) i u):=by
  unfold bitter solid; split; next h'=>
    push_cast; refine prod_congr rfl fun i hi=>?_ ; rcases i with i|i; exact h.exacts ..
    unfold rind; simp only [Sum.elim_inr,H.exacts, reach, Complex.ofReal_sub,Complex.ofReal_one]; exact congr_arg (·-1) (Complex.ofReal_exp _).symm
  exact Complex.ofReal_zero.symm
lemma bitterH (u:Config G n)(i:ℕ): Bumps M.span (bitter Y F h H q u i):= by
  unfold bitter; split; next he=>
    intro s c ht hm hu; apply DifferentiableOn.fun_finsetProd; rintro (i|i) hi
    · exact h.pulse i u s c ht hm hu
    exact ((H.pulse i u s c ht hm hu).cexp).sub_const _
  exact bumps _ _ (differentiableOn_const _)
include h H
lemma bitterP (u:Z)(hu:u∈M.span)(K: Payments.Rates p.B w a b κ): (bell (addr F q) p.B p.supportExponent).MeasureP (fun i V=> bitter Y F h H q V i u) w:=by
  obtain ⟨f,hf,hA⟩:= (h.bounds u hu).afloat; obtain ⟨g,hg,hB⟩:= (H.bounds u hu).afloat
  let A i:= Real.exp κ*f i; let W:= inflation a b κ; let Z:= Sum.elim A (fun i=> 2*g i); let t:= Real.exp (-κ); have ht : t≤1:= Real.exp_le_one_iff.mpr (neg_nonpos.mpr K.heading)
  let μ: Ovens.Label → ℝ:= Sum.elim (fun _=> t) (fun _=>1)
  have hx :Ac.Hit X.patch p.B Z (p.supportExponent+1) W:=fun i=> Cost.sum (AnalyticBridge.VerifiedReset.Quotes.hit_scale (Real.exp_pos κ).le ((bellbook ..).1 hA) i) (AnalyticBridge.VerifiedReset.Quotes.hit_scale zero_le_two ((soot X _ _ _ _).1 hB) i)
  have hG (i:ℕ):g i≤1:= by
    obtain ⟨x,hx⟩:= X.sites i; have he := budget_single (hB x) i
    simp only [softer,if_pos hx] at he; exact (le_mul_of_one_le_left (hg i).1 (Real.one_le_exp (mul_nonneg (add_nonneg p.exponent_pos.le zero_le_one) (Nat.cast_nonneg _)))).trans (he.trans K.soft_limit)
  have hZ i :0 ≤ Z i:= by
    rcases i with i|i; exact mul_nonneg (Real.exp_pos _).le (hf i).1; exact mul_nonneg zero_le_two (hg i).1
  have hp(V:Config G n)(i:Ovens.Label): ‖rind Y h H V i u‖≤ μ i*Z i:= by
    rcases i with i|i; · rw [show μ (Sum.inl i)*Z (Sum.inl i)=f i from (by unfold Z μ A t; simp [← mul_assoc,← Real.exp_add])]; exact (hf i).2 V
    change ‖Complex.exp _-1‖≤1*(2*g i); rw [one_mul]; exact (Complex.norm_exp_sub_one_le (((hg i).2 V).trans (hG i))).trans (mul_le_mul_of_nonneg_left ((hg i).2 V) zero_le_two)
  let b i:= t * ∏ l∈(F i).val,Z l
  refine ⟨b,fun i=>?_,fun i=>?_⟩
  · have hR : 0 ≤ ∏ l∈(F i).val,Z l:= Finset.prod_nonneg fun _ _ => hZ _
    have hh:0≤ b i:= mul_nonneg (Real.exp_pos _).le hR
    refine ⟨hh,fun U=>?_⟩; unfold bitter; split; swap; · exact norm_zero.trans_le hh
    rw [norm_prod]; refine (prod_le_prod (fun _ _ => norm_nonneg _) (fun j _=> hp U j)).trans ?_; rw [prod_mul_distrib]; refine mul_le_mul_of_nonneg_right ?_ hR
    obtain ⟨x,hx⟩:= (F i).property.1; have he: Sum.inl x∈(F i).val:= mem_toLeft.mp hx
    apply (prod_le_prod_of_subset_of_le_one (f:=μ) (singleton_subset_iff.mpr he) (fun i _=> match i with | .inl _=> (Real.exp_pos _).le | .inr _=>zero_le_one) (fun i _ _=> match i with | .inl _=> ht | .inr _=>le_rfl)).trans_eq
    rw [Finset.prod_singleton]; rfl
  let w:= Ac.roots X.patch p.B Z p.supportExponent i
  have hs : SumBudget w (Real.exp W-1) := Ac.forest X.patch p.B p.exponent_pos.le hZ hx K.capital (budget_nonneg (hx 0)) i
  have he:=budget_pull (Subtype.val ∘ F) (Subtype.val_injective.comp F.injective) hs
  rw [show (fun j=> _* b j)=(fun j=> t*w (F j).val) from ?_]; exact budget_loosen (budget_scale (Real.exp_pos _).le he) K.returns
  funext z; unfold bell; dsimp only [addr,Ac.roots,w,skin]
  have hh:= (F z).property.2.1; split_ifs with hy hz
  · unfold b; ring
  · exact False.elim (hz ⟨hh,hy⟩)
  · rename_i hk; exact (hy hk.2).elim
  ring
lemma brittle (K:Payments.Rates p.B w a b κ): Nonempty (Atlas (bell (addr F p) p.B p.supportExponent) M (fun i j u=> solid F p (Y i) j u) (fun _=>w)):= ⟨⟨fun z i V=> bitter Y F h H p V i z,fun d i V=> bitterS Y F h H V i d,fun i V=> bitterH Y F h H V i,fun z hz=> bitterP Y F h H z hz K⟩⟩
end YM.UVExtension.Concert
