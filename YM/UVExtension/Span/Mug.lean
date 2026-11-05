import YM.UVExtension.Span.Rails
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable [NeBot v]
-- Helpers.
open Mask Raw Matter Poll Pond Silica Eider Polar Reserves
include p
lemma logbills {B:ι→LogIndex c f→ℝ}(h:∀ i, Sales (radiusB s) Q.relative Q.ε (roadway (T i) (R i) (radiusB s) Q.halo) (B i) (exCharge (T i) (R i)) (Q.goal L s)) {J:α→LogIndex c f} (he:Injective J)(n:α→ℕ)(hh:∀ i x,exCharge (T i) (R i) (J x)=n x)(hfin :∀ y:ℕ, Set.Finite {x|n x≤y}) (k:ℕ)(u:ℝ)(hp:0≤u) : Swift v (fun i x=> B i (J x)*(1+u*(1+n x))^k):=by
   let fz i x:= B i (J x)*(1+u*(1+n x))^k; obtain ⟨K,hK,hX⟩:= pays (max u 1) (zero_le_one.trans (le_max_right ..)) (2*Q.ε) (mul_pos (by norm_num) Q.usable) (k+1); let r:=Real.exp (2*Q.ε)
   have hx i :SumBudget (fun x=> (1+(n x:ℝ))*fz i x) (K*r*((Fintype.card (Site c):ℝ)*Q.goal L s)):= by
       have hu (x:LogIndex c f): 0 ≤ tariff (B i) (fun x=> (exCharge (T i) (R i) x :ℝ)) (fun _=>0) Q.ε x:= mul_nonneg ((h i).nonneg _) (Real.exp_pos _).le
       have ht : 0≤ Q.relative:=by unfold Target.relative; linarith [Q.bound,Q.usable,Q.pos]
       refine budget_mono (budget_scale (mul_nonneg hK (Real.exp_pos _).le) (budget_pull J he (Swift.spared (h i).hit ht hu (fun j _=> Coat.exChart ..)))) (fun x=>mul_nonneg (by positivity) (mul_nonneg ((h i).nonneg _) (pow_nonneg (add_nonneg zero_le_one (mul_nonneg hp (by positivity))) _))) (fun x=>?_)
       unfold fz Reserves.tariff; simp only [hh,add_zero]; let m:ℝ:=1+n x; let p₀:=max u 1; let t:=1+m*p₀; have hm:0≤m:=by unfold m; positivity
       have ht':1≤p₀:=le_max_right ..; have hg:m≤t:=by unfold t; nlinarith
       have hd:1+u*m≤ t:= by unfold t; calc
          _ ≤ 1+p₀*m:= add_le_add_right (mul_le_mul_of_nonneg_right (le_max_left ..) hm) _
          _ = _:=by ring
       have hy :m*(1+u*m)^k≤ K*Real.exp (2*Q.ε*m):=(le_trans (mul_le_mul hg (pow_le_pow_left₀ (by positivity) hd k) (by positivity) (hm.trans hg)) ((pow_succ' ..).symm.le.trans (hX m hm))) -- succ
       calc
          _ = B i (J x)*(m*(1+u*m)^k):=by unfold m; ring
          _ ≤ B i (J x)*(K*Real.exp (2*Q.ε*m)) := mul_le_mul_of_nonneg_left hy ((h i).nonneg _)
          _ = _:=by unfold m r; rw [mul_add,mul_one,Real.exp_add]; ring
   obtain ⟨i,_⟩:= (show ∀ᶠ i in v,True from by simp).exists; refine Swift.ranked (w:=fun _=>n) ⟨_,budget_nonneg (hx i),Eventually.of_forall hx⟩ (fun i=> ?_)
   let a k x:= if n x ≤ i then fz k x else 0
   have hy k : SumBudget (a k) (K*r*((Fintype.card (Site c):ℝ)*Q.goal L s)):=budget_mono (hx k) (fun x=>by unfold a fz; split <;> first|exact le_rfl|exact mul_nonneg ((h k).nonneg _) (pow_nonneg (by positivity) _))
      (fun x=>by unfold a; split; exact le_mul_of_one_le_left (mul_nonneg ((h k).nonneg _) (pow_nonneg (by positivity) _)) (by simp); exact (hx k).1 _)
   refine ⟨⟨_,Eventually.of_forall hy⟩,fun ε he=>⟨(hfin i).toFinset,?_⟩⟩
   filter_upwards with k; change SumBudget (fun x=> if x∈ _ then 0 else a k x) _; rw [show (fun x=>ite _ 0 (a k x))=(fun _=>0) from ?_]; simp [SumBudget,he.le]
   ext x; simp only [Set.Finite.mem_toFinset]; by_cases h:n x ≤ i <;> simp [a,h]
-- restrict Ledger payments sales
omit p [NeBot v] in lemma loosens {B:ℕ}{a b c':ℝ}{w:κ→ℝ}{X:κ→Support c}{d:κ→ℕ}(j:α→κ)(hi:Injective j)(h:Sales B a b X w d c') :Sales B a b (X∘j) (w∘j) (d∘j) c':=⟨fun x=>h.nonneg _,fun x=> budget_pull _ hi (h.hit x)⟩

-- for any family into LogIndex with compact level & uniform card. Then gives Fee automatically. 
def pond (i): Utopia (H i) k u d r N χ:= ((p.realm.granted c f S (T i) (R i) _ (H i) (p.rails _) rfl).1).some
lemma moonlight (J:α→ LogIndex c f)(hJ:Injective J)(n:α→ℕ)(hh:∀ i x,exCharge (T i) (R i) (J x)=n x)(hfin :∀ y:ℕ, Set.Finite {x|n x≤ y}): Lloyd p (fun x=> Sum.inr (Sum.inr (.inl (J x)))):=by
    let T' i:= p.pond i; let B i:=(p.pond i).goalsL; let W' i:=(H i).w
    let g (j:LogIndex c f): Alphabet c f:=.inr (.inl j); have hg:Injective g:= fun x y he=> Sum.inl_injective (Sum.inr_injective he)
    have hp i: Sales (radiusB s) Q.relative Q.ε (roadway (T i) (R i) (radiusB s) Q.halo) (B i) (exCharge (T i) (R i)) (Q.goal L s):= loosens g hg (T' i).uses
    have ht i: Sales (radiusB s) Q.relative Q.ε (roadway (T i) (R i) (radiusB s) Q.halo) (W' i) (exCharge (T i) (R i)) (Q.goal L s):= loosens g hg (H i).fares
    obtain ⟨m,hv⟩:= (show ∀ᶠ i in v,True from by simp).exists
    have hr:0≤r:=zero_le_one.trans (T' m).active
    let A := Finset.univ.sup (fun i:Support c=>coverNumber (radiusB s) i);
    let u:=r*(1+A); have hu:0≤u:= mul_nonneg hr (by positivity); let f i x:= B i (J x)*(1+u*(1+n x))^k; have hf : Swift v f:= logbills p hp hJ n hh hfin k u hu
    let b i x:= W' i (J x)*(1+(0:ℝ)*(1+n x))^(0:ℕ); have hb : Swift v b:= logbills p ht hJ n hh hfin 0 0 le_rfl
    obtain ⟨r',hr'⟩:=hf.books
    refine ⟨_,hb.plus hf,?_⟩; filter_upwards [hr'] with i hi j
    let Q' : Head S:= Sum.inr (Sum.inr (Sum.inl (J j)))
    have hx :0 ≤ b i j:=by unfold b; rw [pow_zero,mul_one]; exact (ht i).nonneg _
    change Lodge p i Q' (b i j+f i j); constructor
    · intro F X hs hv hu hh v Y; apply (Cash.voice (H i) X hs hv hh Y Q' v).trans; unfold b; rw [pow_zero,mul_one]; exact le_add_of_nonneg_right (hi.1 j)
    intro E _ _ _ F X Y P τ S' v hs hv hu' hm hX he ht' n'
    have hL:=((T' i).stream E F X Y P S' τ v hs hv hu' hm hX he n' Q' ht')
    refine hL.trim.climb ((le_add_of_nonneg_left hx).trans' ?_) le_rfl
    have he (y:Support c): (coverNumber (radiusB s) y :ℝ)≤A:= by exact_mod_cast le_sup (f:=fun i=>coverNumber (radiusB s) i) (mem_univ y)
    unfold f; change (B i (J j))*_ ≤ _; apply mul_le_mul_of_nonneg_left _ ((hp i).nonneg _); apply pow_le_pow_left₀ (add_nonneg zero_le_one hL.pos)
    have he' : X.B=radiusB s:= congr_arg _ hs
    rw [he']; unfold spanW Clutch.twigs lengths; simp only [Q',Sum.elim,hh]; apply add_le_add_right
    unfold u; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hr
    have hp:0≤(A:ℝ)*n j:=by positivity
    have he:=he (footprints (T i) (R i) Q.halo (radiusB s) (.inr (.inl (J j))))
    nlinarith only [he,hp]
omit p [NeBot v] in lemma ledger_sets (k : ℕ)(n:ℕ): Set.Finite {x:Ledger f k|x.1≤n}:=by
    let b (i:ℕ):Finset (Ledger f k):= Finset.univ.image (Sigma.mk i)
    refine (Finset.finite_toSet ((Finset.range (n+1)).biUnion b)).subset ?_; rintro ⟨v,u⟩ h; exact Finset.mem_biUnion.mpr ⟨v,mem_range.mpr (Nat.lt_succ_of_le h),Finset.mem_image_of_mem _ (mem_univ _)⟩
lemma legsP : Lloyd p (fun x: Miniature c f ⊕ ChainIndex f=> Sum.inr (.inr (.inl (Sum.inr x)))):=by
   let F (x: Miniature c f ⊕ ChainIndex f): LogIndex c f:= Sum.inr x
   let g: Miniature c f ⊕ ChainIndex f→ℕ:= Sum.elim (fun _=>0) (basisCharge f); refine moonlight p F Sum.inr_injective g ?_ ?_
   · intro i x; rfl
   intro y
   let h {α β:Type}(a:α→ℕ)(b:β→ℕ)(hp:Set.Finite {x|a x≤y})(he:Set.Finite {x|b x≤y}):Set.Finite {x|Sum.elim a b x≤y}:=by
     refine ((hp.image (Sum.inl (β:=β))).union (he.image Sum.inr)).subset ?_; rintro (x|x) hx; exact Or.inl ⟨x,hx,rfl⟩; exact Or.inr ⟨x,hx,rfl⟩
   apply h _ _ (Set.toFinite _); unfold basisCharge; apply h _ _ (ledger_sets ..); apply h _ _ (ledger_sets ..); apply h _ _ (ledger_sets ..); exact h _ _ (Set.toFinite _) (ledger_sets ..)
end Score
end YM.UVExtension.Span
