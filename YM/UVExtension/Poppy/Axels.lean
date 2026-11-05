import YM.UVExtension.Poppy.Field
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter Metric Lattice Extraction Fallow
open scoped Topology BigOperators ContDiff Classical
variable {S:Schedule}{n m k N:ℕ}{x y u: Tabletop n}
section rates
variable {t:ℝ}(ht:0<t)(F:Tabletop n→ℂ) {b:ℝ}(i:Axel n)(x:Tabletop n)(w:ℂ)
include ht
lemma force (l:ℕ)(h:∀ k:ℕ,k < l→ ‖climbing t F i (x+k • hike i)-w‖≤ b) :
    ‖F (x+l • hike i)-F x - ( (↑l*t:ℝ):ℂ)*w‖ ≤ l*t*b:=by
   induction l with
   | zero=> simp
   | succ l ih=>
      let u:= x+l • hike i; have hp := ih (fun k hk=>h k (hk.trans l.lt_succ_self)); rw [add_smul,one_smul,← add_assoc]; push_cast
      change ‖F (u+hike i)-F x-_*w‖ ≤ _
      rw [show _- ( (↑l+1:ℂ)*(t:ℂ))*w= (F (u+hike i)-F u-(t:ℂ)*w)+(F u-F x- ((↑l*t:ℝ):ℂ)*w) from (by push_cast; ring : F (u+hike i)-F x - ((↑l+1:ℂ)*(t:ℂ))*w=_)]
      exact (norm_add_le ..).trans ((add_le_add ((beat ht (F:=F) (w:=w) (x:=u) i).trans_le (mul_le_mul_of_nonneg_left (h l l.lt_succ_self) ht.le)) hp).trans_eq (by ring))
lemma moth (l:ℕ)(p : 0 < l)(h:∀ k:ℕ,k < l→ ‖climbing t F i (x+k • hike i)-w‖ ≤ b):
   ‖( ( (↑l*t:ℝ):ℂ))⁻¹*(F (x+l • hike i)-F x)-w‖ ≤ b:=by
   let z:ℝ:= l*t; have hz:0<z:= mul_pos (by exact_mod_cast p) ht; have hp:= force ht F i x w l h
   have hv : ( (z:ℂ))⁻¹ * (F (x+l • hike i)-F x) - w= ((z:ℂ))⁻¹*(F (x+l • hike i) - F x - (z:ℂ)*w):=by rw [mul_sub (_⁻¹) (F (x+l • hike i)-F x) _, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr hz.ne')]
   rw [hv,norm_mul,norm_inv,Complex.norm_real, Real.norm_of_nonneg hz.le]
   exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (inv_mul_cancel_left₀ hz.ne' b)
end rates

variable {A: Set (Points n)}(h:IsOpen A) {F:ℕ→ Tabletop n→ℂ} {f:Points n→ℂ} (hp: Meets A (Ink S F) f)
lemma alba (U:Tabletop n→ℂ)(N:ℕ)(w:Tabletop n): U (Extraction.address (S.a N) (tag (S.a N) w))=U w:=by rw [Extraction.address_matched (S.a_pos _)]
lemma beating (S:Schedule)(r:ℝ)(hr:0<r): ∃ l:ℕ→ℕ,(∀ᶠ N in atTop, 0 < l N)∧(∀ N,(l N:ℝ)*S.a N ≤ r)∧ Tendsto (fun i=> (↑(l i):ℝ)*S.a i) atTop (𝓝 r):=by
   let l (i:ℕ):=Nat.floor (r/S.a i); have hP(i):(l i:ℝ)*S.a i ≤ r:= (le_div_iff₀ (S.a_pos _)).mp (Nat.floor_le (div_pos hr (S.a_pos _)).le)
   have ht : Tendsto (fun i=> (↑(l i):ℝ)*S.a i) atTop (𝓝 r):=by
       refine tendsto_of_tendsto_of_tendsto_of_le_of_le (f:=fun i=> ( (l i:ℝ))*S.a i) (g:=fun i=> r-S.a i) (by simpa only [sub_zero] using (tendsto_const_nhds (x:=r)).sub S.shrinks) (tendsto_const_nhds (x:=r)) (fun i=> ?_) hP
       have hh:= (div_lt_iff₀ (S.a_pos i)).mp (Nat.lt_floor_add_one (r/S.a i)); unfold l; linarith only [hh]
   exact ⟨l,(ht.eventually (lt_mem_nhds hr)).mono fun n hn=>by have he:0<(l n:ℝ):=pos_of_mul_pos_left hn (S.a_pos n).le; exact_mod_cast he,hP,ht⟩
include hp h
lemma visiting {x:Points n}(hx:x∈A)(k:ℕ→ Tabletop n)(he:Tendsto (fun i=> tag (S.a i) (k i)) atTop (𝓝 x)): Tendsto (fun i => F i (k i)) atTop (𝓝 (f x)):=by
   obtain ⟨K,hK,hz,hU⟩:= exists_compact_subset h hx; have hx:=he.eventually (mem_interior_iff_mem_nhds.mp hz); have ht:= ((hp.continuousOn _ ‹x∈A›).continuousAt (h.mem_nhds ‹_›)).tendsto.comp he
   apply Metric.tendsto_nhds.mpr; intro ε hε; filter_upwards [hp.uniform K hU hK (ε/2) (by positivity),hx,Metric.tendsto_nhds.mp ht (ε/2) (by positivity)] with i hi he ht; let v:=tag (S.a i) (k i); have hy:=hi _ he; unfold Ink at hy; rw [alba (F i) i (k i)] at hy; exact (dist_triangle _ (f v) _).trans_lt ((add_lt_add hy ht).trans_eq (add_halves ε))
omit hp
variable (i:Axel n) {x:Points n}(hx:x∈A)(ho:oscillation A (Ink S (fun m=> climbing (S.a m) (F m) i)))
local notation "Y"=> fun m=> climbing (S.a m) (F m) i
local notation "Z"=> (fun m=> Extraction.address (S.a m) x)
include ho hx
-- actual strips positive and negative from this x.On all endpoints crude.Osc.Chain.
lemma strip (ε:ℝ)(he:0<ε): ∃ δ:ℝ,0<δ ∧ Metric.closedBall x δ⊆ A∧∀ᶠ m:ℕ in atTop,∀ k:Tabletop n, dist (tag (S.a m) k) (tag (S.a m) (Z m)) ≤ δ → ‖(Y) m k- (Y) m (Z m)‖ ≤ ε:=by
   obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp (h.mem_nhds hx); let K:=Metric.closedBall x (r/2); have hk :K⊆A:= (Metric.closedBall_subset_ball (half_lt_self hr)).trans hR
   obtain ⟨δ,hδ,hO⟩:=ho K hk (isCompact_closedBall ..) ε he; let q:=min (δ/2) (r/4); have hq:0<q:=lt_min (half_pos hδ) (by positivity); have hz:q ≤ r/4:= min_le_right ..
   refine ⟨q,hq,(Metric.closedBall_subset_closedBall (show q ≤ r/2 by linarith only [hz,hr])).trans hk,?_⟩
   filter_upwards [hO,Metric.tendsto_nhds.mp (chosen (S:=S) x) (r/4) (by positivity)] with m hm hx k hp
   let p:= tag (S.a m) (Z m); have hh: dist p x < r/4:=hx; have hk': p∈K:= Metric.mem_closedBall.mpr (by linarith)
   let t:= tag (S.a m) k; have hT := (dist_triangle t p x).trans (add_le_add hp hh.le); have hj:t∈K:= Metric.mem_closedBall.mpr (by change dist t x ≤r/2; linarith only [hT,hz]); have hw:= hm t hj p hk' (hp.trans_lt ( lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ)))
   dsimp only [t,p,Ink] at hw; rw [Extraction.address_matched (S.a_pos m), Extraction.address_matched (S.a_pos _),dist_eq_norm] at hw; exact hw.le
set_option quotPrecheck false
local notation "U"=> Points.direction i.1 i.2
omit h hx ho in
private lemma unit_ (i:Axel n): ‖Points.direction i.1 i.2‖=1:=by simp [Points.direction]
include hp
lemma slopeEstimate (ε:ℝ)(he:0<ε): ∃ δ:ℝ,0<δ ∧∀ t:ℝ,t ≠ 0 → |t|≤δ → ∃ y:ℕ→ℂ, Tendsto y atTop (𝓝 ( (t:ℂ)⁻¹*(f (x+t • U)-f x)))∧∀ᶠ m in atTop,‖y m - (Y) m (Z m)‖ ≤ ε := by
   obtain ⟨δ,hδ,hK,hZ⟩:= strip (F:=F) h _ hx ho ε he
   refine ⟨δ,hδ,fun t ht hh=>?_⟩
   have hz:x+t • U ∈ A := hK (Metric.mem_closedBall.mpr (by rw [dist_eq_norm,add_sub_cancel_left,norm_smul,unit_,mul_one]; exact hh))
   let V m:= tag (n:=n) (S.a m); have hm:= chosen (S:=S) x; have hk:=visiting h hp hx Z hm
   rcases lt_or_gt_of_ne ht with hi|hi
   · rw [abs_of_neg hi] at hh; obtain ⟨l,hl,hL,hP⟩:= beating S (-t) (neg_pos.mpr hi); let A m:= (↑(l m):ℝ)*S.a m
     let Q m:= Z m- l m • hike i; have he m: Q m+ l m • hike i= Z m:=sub_add_cancel ..
     have hv : Tendsto (fun m=> V m (Q m)) atTop (𝓝 (x+t • U)):=by
       unfold V Q; simp_rw [subtract_tag]; simpa only [neg_smul,sub_neg_eq_add] using hm.sub (hP.smul_const U)
     let v m:= F m (Q m); have hp':=visiting h hp hz Q hv; let p m:= ( (A m:ℂ))⁻¹ * (F m (Z m)- v m)
     have hy:Tendsto p atTop (𝓝 ((↑(-t):ℂ)⁻¹*(f x- f (x+t • U)))):= (((Complex.continuous_ofReal.tendsto _).comp hP).inv₀ (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr ht))).mul (hk.sub hp')
     have hx : ((↑(-t):ℂ)⁻¹*(f x- f (x+t • U))) = (t:ℂ)⁻¹ * (f (x+t • U)-f x):=by push_cast; rw [inv_neg, neg_mul, ← mul_neg,_root_.neg_sub]
     refine ⟨p,hx ▸ hy,?_⟩
     filter_upwards [hl,hZ] with m ht hp; have hM:= moth (b:=ε) (S.a_pos m) (F m) i (Q m) ((Y) m (Z m)) (l m) ht ?_
     · rw [he] at hM; exact hM
     intro k hk; apply hp; let r:= l m-k; have he: Z m= Q m+k • hike i+r • hike i:=(he m).symm.trans (by rw [add_assoc,←add_smul,add_tsub_cancel_of_le hk.le]); rw [show dist _ _ = dist (V m (Z m)) (V m (Q m+k • hike i)) from dist_comm ..]; conv_lhs => arg 1; rw [he]; unfold V
     change dist _ (tag _ _ )≤_; rw [lengthP (S.a_pos _)]; exact ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (show r≤l m from Nat.sub_le ..)) (S.a_pos _).le).trans_eq (mul_comm ..)).trans ((hL m).trans hh)
   obtain ⟨l,hl,hL,hP⟩:= beating S t hi; let A m:= (↑(l m):ℝ)*S.a m; let Q m:= Z m+ l m • hike i
   let v m:= F m (Q m); have hv : Tendsto (fun m=> V m (Q m)) atTop (𝓝 (x+t • U)):=by unfold V Q; simp_rw [tagged]; exact hm.add (hP.smul_const U)
   have hp':= visiting h hp hz Q hv; let p m:= ( (A m:ℂ))⁻¹ * (v m- F m (Z m)); refine ⟨p, (((Complex.continuous_ofReal.tendsto _).comp hP).inv₀ (Complex.ofReal_ne_zero.mpr hi.ne')).mul (hp'.sub hk),?_⟩
   filter_upwards [hl,hZ] with m hm hh'; refine moth (S.a_pos m) (F m) i (Z m) _ _ hm (fun k hk=> ?_); apply hh'; rw [lengthP (S.a_pos _)]; rw [abs_of_pos hi] at hh; exact ((mul_le_mul_of_nonneg_left (by exact_mod_cast hk.le) (S.a_pos m).le).trans_eq (mul_comm (S.a m) (l m:ℝ))).trans ((hL _).trans hh)
end YM.UVExtension.Poppy
