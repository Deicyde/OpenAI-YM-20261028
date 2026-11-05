import YM.RemainderComparison.Halo.Vireo

/-!
 # Extract earned smooth rescalings even on zero-volume budgets.

 A second extraction on any hard clusters with MORE vertices, no
 assumption they're attached to analytic chart in any way.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Graft Cascade Lyric Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) (E:Set ℕ)(w:ℕ→ℝ){T' S' p' δ B' τ ε:ℝ}
local notation "Z" => radiusB x
local notation "C'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S C' (ConnectedActivityE6.lengths T R)
variable (C₁ A₁:ℝ)
variable (X : ℝ)
local notation "rail" => rails H N.conduit E w C₁ A₁
local notation "p₀" => melod M H rail X n
local notation "TOL" => Lyric.mulScale τ⁻¹ l
section
variable (z:H.fragrances)(i:Syllable M H z)

def dyed := ∃ a p, inherited S E p∧ p∈ (z.2 a).val\ (i a).reach

def gross := ∑ a, ((z.2 a).val\(i a).reach).card
local notation "G₀" => gaugeG (S:=S) E T' S'
omit [Fintype ι] in
lemma charges (hp:dyed M H E z i)(hh:1+m≤gross M H z i)(ht: S' ≤ T')(hv:1≤S') : T'*S'^m ≤ ∏ a,merit M H G₀ (z.2 a) (i a):=by
   let U (a:Option (Fin z.1)):= (z.2 a).val\(i a).reach
   let f (i':Head S):=G₀ i'
   have hh' z:S' ≤ f z:=by unfold f gaugeG; split; exact ht; exact le_rfl
   obtain ⟨a,p,hS,hP⟩:=hp
   let F (b:Option (Fin z.1)):= if a=b then (U b).erase p else U b
   let g b:= ∏ i ∈ F b,f i
   have h : (∑ a,(F a).card)+1=gross M H z i:=by
      unfold gross; change _=∑a,(U a).card; rw [← add_sum_erase _ _ (mem_univ a), ← add_sum_erase _ _ (mem_univ a)]
      have hf:#(F a)+1=#(U a):= by unfold F; rw [if_pos rfl]; exact card_erase_add_one (s:=U a) hP
      rw [add_right_comm (#(F a)),hf]; congr 1; exact Finset.sum_congr rfl (fun i hi=> by unfold F; rw [if_neg (ne_of_mem_erase hi).symm])
   have hS':0≤S':=zero_le_one.trans hv
   have hp' : S'^m≤ ∏ b,g b:=by
      apply le_trans (pow_le_pow_right₀ hv (show m ≤ ∑ a,#(F a) by omega)) _
      rw [← Finset.prod_pow_eq_pow_sum]; apply prod_le_prod (fun _ _=> pow_nonneg hS' _); intro a ha
      unfold g; rw [← prod_const]; exact prod_le_prod (fun i _=>hS') (fun i _=> hh' i)
   apply (mul_le_mul_of_nonneg_left hp' (hS'.trans ht)).trans_eq
   rw [← mul_prod_erase _ _ (mem_univ a), ← mul_prod_erase _ _ (mem_univ a)]
   unfold merit; change T'*(g a*_)=(∏ i'∈ U a,f i')*_
   have hq:T'*g a=∏ i'∈ U a,f i':=by
      unfold g F; rw [if_pos rfl,← show f p=T' from if_pos hS]; exact mul_prod_erase _ f hP
   rw [← mul_assoc,hq]; apply congrArg; exact Finset.prod_congr rfl (fun j hj=> by unfold g F; rw [if_neg (ne_of_mem_erase hj).symm])
omit [Fintype ι] in
lemma barren (hp:dyed M H E z i)(h:Presents R E w 0) : Lyric.Bill M H p₀ z l j i J=0:=by
   obtain ⟨a,p,⟨u,hu,rfl⟩,hb⟩:=hp
   have hv : w u=0:= le_antisymm (h.roof _) (h.pay _); have hh : rail (Opacity.key S u)=0:=by unfold rails; rw [weather_at _ hu, hv,mul_zero]
   unfold Lyric.Bill Lyric.dividend Lyric.adjectives; rw [Finset.prod_eq_zero (mem_univ a) (show 2^j * p₀ (z.2 a) (i a)=0 from mul_eq_zero_of_right _ ?_),mul_zero,mul_zero,mul_zero]
   unfold melod; split; next => rw [Finset.prod_eq_zero hb hh,mul_zero,zero_mul]
   next=> rfl
end

variable {P':Type} [Fintype P']{X':P'→ Site f}{Y:ι→ Finset P'} (hp: Lyric.Scale X' Y M l m σ B' S)

lemma remits (P : H.ThinP→ Drums M S→ℝ)(V:(z:H.fragrances)→Syllable M H z→Prop)
    (R : Ac.Hit (Captain.reachability (H:=H)) Z
      (fun z=>∑ w:Syllable M H z, if V z w then Lyric.Bill M H P z TOL j w s else 0) a δ)
    (hf:∀ i, 0 ≤ l i)(he:1≤τ)(hQ:Lyric.Paid M H χ N P)(k:ℕ) :
    Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ w:Syllable M H z, if V z w ∧ Lyric.notes M H z w≤k then Lyric.Bill M H P z l j w s else 0) a (τ^k *δ):=by
   have hz:0<τ:= zero_lt_one.trans_le he
   have hp z w:0≤Lyric.Bill M H P z l j w s:= mul_nonneg (prod_nonneg fun i _=> prod_nonneg fun z _=>hf _) (dividend_nonneg M H χ hQ z w)
   have ht z w: Lyric.Bill M H P z TOL j w s= τ⁻¹^ Lyric.notes M H z w * Lyric.Bill M H P z l j w s:=by unfold Lyric.Bill; rw [Lyric.toll,mul_assoc]
   intro i; refine budget_mono (budget_scale (pow_pos hz k).le (R i)) (fun z=>?_) (fun z=>?_)
   · dsimp only; split
     · exact mul_nonneg (sum_nonneg fun w _=> by split; exact hp _ _; exact le_rfl) (Real.exp_pos _).le
     exact le_rfl
   dsimp only; split; next h=>
     rw [← mul_assoc,Finset.mul_sum]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
     refine sum_le_sum ?_; intro w h; rw [ht]; split_ifs
     next ht hv=> rw [← mul_assoc]; exact le_mul_of_one_le_left (hp z w) (by rw [inv_pow,← div_eq_mul_inv]; exact (one_le_div (by positivity)).2 (pow_le_pow_right₀ he ht.2))
     next ht hv=> exact False.elim (hv ht.1)
     next h₁ h₂=> exact mul_nonneg (pow_nonneg hz.le _) (mul_nonneg (pow_nonneg (inv_nonneg.mpr hz.le) _) (hp _ _))
     next=>rw [mul_zero]
   next=>rw [mul_zero]
local notation "F'" => (τ*δ)⁻¹
variable {γ :ℝ}
include hp
lemma wishes (hl:R.p.B ≤ 2*Z)(hC:radiusCost Q L σ)(h:Presents R E w δ)(he:Sales Z Q.relative Q.ε (regularFoot S.ratio Q.halo Z R) w (regularExtra R) (|cost L Q x| *δ))
    (hr:Quarry H N.conduit A C₁ A₁ X n) (hv:1≤τ) (hS:1 ≤ S')(hy:0 ≤ C₁)(hm:δ ≤ 1)(hA:0≤A₁)(hX:0 ≤ X)(hd:0<γ)
    (ht:first (S'*A₁) (C').rootHit τ⁻¹ C₁ (|cost L Q x|) (hike Q x m (τ⁻¹ *B')) ≤ γ)
    (hw:τ*δ*S' ≤ 1) (hg:degreePrice Z γ Q.δ ≤ 1/2) (hzL:a+ε+ε≤ Q.exp)(hQ:0 ≤ a)(hε:0<ε)
    (hβ:degreePrice Z (rebate Q X γ j n) ε≤1/2)(K k J:ℕ) :
    Ac.Hit (Captain.reachability (H:=H)) Z (fun z=>∑ i:Syllable M H z, if (dyed M H E z i ∧ 1+k≤gross M H z i) ∧ Lyric.notes M H z i≤K then
       Lyric.Bill M H p₀ z l j i J else 0) a (τ^K*(τ*δ*(S'^k)⁻¹*(collars G ε x j J*(rebate Q X γ j n * (1-1/2)⁻¹)))):=by
   by_cases hi:0<δ
   swap; · have ht:δ=0:= le_antisymm (le_of_not_gt hi) h.positive
           subst δ; have he z: (∑ i:Syllable M H z, if (dyed M H E z i∧ 1+k≤gross M H z i) ∧ Lyric.notes M H z i≤K then Lyric.Bill M H p₀ z l j i J else 0)=0:=by
             apply sum_eq_zero; intro i _; split
             next ht=> exact barren M H χ N l E w C₁ A₁ X z i ht.1.1 h
             next=> rfl
           intro x; simp_rw [he]; simp [SumBudget]
   let r:= TOL
   have hh:0<τ:= zero_lt_one.trans_le hv; have he':0<S':=zero_lt_one.trans_le hS
   let f:= gaugeG (S:=S) E F' S'; have hw' : S' ≤ F':=by rw [← one_div]; apply (le_div_iff₀ (mul_pos hh hi)).2; rw [mul_comm]; exact hw
   have hf i : 0≤f i:=by unfold f gaugeG; split_ifs <;> positivity
   have hb:= scaled M l hp (inv_pos.mpr hh).le
   have hF:= rays (q:=q) M H r hb hl hC
   have hL:first (S'*A₁) (C').rootHit F' C₁ (|cost L Q x| *δ) (hike Q x m (τ⁻¹ * B')) ≤ γ:= by
      apply le_trans _ ht; unfold first; apply le_of_eq; field_simp
   have hpX:= rails_nonneg H N.conduit E w C₁ A₁ h hy hA
   have ht' := Halo.earns M H χ N (rail) n X hX hpX (fun M p=>hr.ready M E w δ h hm p)
   have he := redwood M H N.conduit r E w C₁ A₁ F' S' h (inv_pos.mpr (mul_pos hh hi)).le he'.le hy hA hb.currency he hF hL hd hg
   have hx:= boats M H rail f n X r hX (prize M r rail f hb.currency hpX hf) hε hzL he hβ
   convert! remits M H χ N l p₀ _ (Lyric.run M H χ p₀ r (merit M H f) ht' hb.currency (fun p i=>prod_nonneg fun i _=> hf i) hQ J hx
     (fun z i=> dyed M H E z i∧1+k≤gross M H z i) (τ*δ*(S'^k)⁻¹) (by positivity) (fun z i ⟨hP,hK⟩=>?_)) hp.currency hv ht' K using 1
   · ext z; refine Finset.sum_congr rfl fun i _=>?_ ; split_ifs <;> rfl
   apply le_trans _ (mul_le_mul_of_nonneg_left (charges M H E z i hP hK hw' hS) (by positivity)); exact le_of_eq (by field_simp)
end YM.RemainderComparison.Halo
