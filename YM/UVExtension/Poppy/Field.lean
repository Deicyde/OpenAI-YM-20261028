import YM.UVExtension.Fallow.Plow
import YM.Extraction.Equicontinuity
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Poppy
open Finset Set Function Filter Metric Lattice Extraction Fallow
open Difference (advance extent)
open scoped Topology BigOperators ContDiff Classical
variable {S:Schedule}{n m k N:ℕ}{x y u: Tabletop n}
open scoped Nat

lemma in_step (a:Axel n) (m:ℕ) : x+m • hike a= advance x a.1 a.2 m:=by
   ext1 i; by_cases h:i=a.1 <;> simp [advance,hike,Work.D03.jump,h]
lemma widen (x y : Tabletop n) (t:ℝ) : dist (tag t x) (tag t y)^2 = ∑ i : Fin n × Axis,(t*(x i.1 i.2-y i.1 i.2:ℤ))^2:=by
  rw [dist_eq_norm,← Points.flatten.norm_map,EuclideanSpace.real_norm_sq_eq]; simp only [map_sub,PiLp.sub_apply]; refine Finset.sum_congr rfl fun i _ => ?_; change (_ * _ - _ * _) ^ 2 = _; simp only [Int.cast_sub,mul_sub]
lemma lengthP {t:ℝ}(ht:0<t)(i:Axel n)(l:ℕ): dist (tag t (x+l • hike i)) (tag t x)= t*l:=by rw [in_step]; exact extent _ _ _ _ t ht
lemma tagged (a:Axel n)(t:ℝ)(x:Tabletop n)(i:ℕ) : Extraction.tag t (x+i • hike a)= Extraction.tag t x+(↑i*t) • Points.direction a.1 a.2:=by
   induction i with
   | zero=> simp
   | succ i ih=> rw [add_smul,one_smul,← add_assoc, show tag t (x+i • hike a+hike a)=_ from Work.D03.tag_add_jump t (x+i • hike a) a.1 a.2,ih,Nat.cast_add,Nat.cast_one,add_mul,one_mul, add_smul, add_assoc] -- hike expand
lemma subtract_tag (a:Axel n)(t:ℝ)(x:Tabletop n)(i:ℕ): Extraction.tag t (x-i • hike a)= Extraction.tag t x- (↑i*t) • Points.direction a.1 a.2:=by
   apply eq_sub_of_add_eq; rw [← tagged,sub_add_cancel]

section oscillatory
variable {S :Schedule}{A:Set (Points n)} {ε:ℝ} {t:ℝ} (ht:0<t) {F:Tabletop n→ℂ}{b:ℝ}
def capping (t b:ℝ)(F:Tabletop n→ℂ)(A:Set (Points n)) := ∀ (a:Axel n) (x:Tabletop n), Extraction.tag t x∈A → ‖climbing t F a x‖ ≤ b
include ht
lemma beat {x:Tabletop n}{w:ℂ}(a:Axel n): ‖F (x+hike a)- F x-(t:ℂ)*w‖=t*‖climbing t F a x-w‖:=by
   rw [show F (x+hike a)- F x-(t:ℂ)*w=(t:ℂ)*(climbing t F a x-w) by unfold climbing; rw [mul_sub,mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr ht.ne')]]; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
lemma beat1 (h:capping t b F A)(x:Tabletop n)(i:Axel n)(hx:tag t x∈A): dist (F (x+hike i)) (F x) ≤ t*b:=by rw [dist_eq_norm]; simpa only [mul_zero,sub_zero] using (beat ht (F:=F) (w:=0) (x:=x) i).trans_le (mul_le_mul_of_nonneg_left (show ‖climbing t F i x-0‖ ≤ b from by rw [sub_zero]; exact h i x hx) ht.le)
lemma localWalk (h:capping t b F A)(x:Tabletop n)(i:Axel n)(k:ℕ) (hx:∀ l:ℕ,l ≤ k→ tag t (x+l • hike i)∈ A): dist (F (x+k • hike i)) (F x) ≤ b*dist (tag t (x+k • hike i)) (tag t x):=by
   rw [lengthP ht]
   induction k with
   | zero=> simp
   | succ k ih=>
      let X:=x+k • hike i; have he:=ih (fun l hl=>hx _ (hl.trans k.le_succ)); rw [add_smul,one_smul, ← add_assoc]
      push_cast
      exact (dist_triangle _ (F X) _).trans ((add_le_add (beat1 ht h X _ (hx k k.le_succ)) he).trans_eq (by ring))
-- grid rectangle replacing one point at time
omit ht
private def via (x y:Tabletop n)(s:Finset (Fin n× Axis))(i:Fin n)(a:Axis):ℤ:=if (i,a)∈s then x i a else y i a
private lemma replaces (t : ℝ) (s u : Finset (Fin n × Axis)) :
    dist (tag t (via x y s)) (tag t (via x y u)) ≤ dist (tag t x) (tag t y) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
  simp_rw [widen]; apply Finset.sum_le_sum; intro p _
  unfold via; split_ifs <;> simp <;> first | rfl | positivity | ring_nf; rfl
include ht
lemma hop (h:capping t b F A)(hb:0≤b){K:Set (Points n)}(x y:Tabletop n)(hK:tag t y∈K){r:ℝ}(hr:cthickening (2*r) K⊆A)(hx: dist (tag t x) (tag t y)≤ r) : dist (F x) (F y) ≤ (n*(4:ℝ)*b)* dist (tag t x) (tag t y):=by
   let d:=dist (tag t x) (tag t y)
   let W:= via x y
   have hk (s u): dist (tag t (W s)) (tag t (W u)) ≤ d:= replaces t s u
   have hy: W ∅=y:=by ext;simp [W,via]
   have hS{s u:Finset (Fin n×Axis)}(i:Fin n)(j:Axis)(l:ℕ)(he:W s=advance (W u) i j l): dist (F (W s)) (F (W u)) ≤ b*d:=by
      let a:Axel _ := (i,j); have hh: W s=W u+l • hike a:=he.trans (in_step a l|>.symm)
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (hk s u) hb); rw [hh]; refine localWalk ht h _ _ _ ?_; intro k hv; apply hr; refine mem_cthickening_of_dist_le _ _ _ K hK ((dist_triangle _ (tag t (W u)) _).trans ?_); rw [lengthP ht]; have hp:t*l ≤ d:=by have ha:= hk s u; rw [hh,lengthP ht] at ha; exact ha
      have hh':t*k ≤ t*l:=mul_le_mul_of_nonneg_left (by exact_mod_cast hv) ht.le
      have hY:= hk u ∅; rw [hy] at hY; exact (add_le_add (hh'.trans (hp.trans hx)) (hY.trans hx)).trans_eq (two_mul ..).symm
   have hs (s): dist (F (W s)) (F y)≤ (s.card:ℝ)*(b*d):=by
      induction s using Finset.induction_on with
      | empty=> simp [hy]
      | @insert u s hu ih=>
         obtain ⟨i,j⟩:=u
         rw [Finset.card_insert_of_notMem hu,Nat.cast_add,Nat.cast_one,add_mul,one_mul, add_comm ((s.card:ℝ)*_)]
         refine (dist_triangle _ (F (W s)) _).trans (add_le_add ?_ ih)
         rcases le_total (x i j) (y i j) with h|h
         · rw [dist_comm]; apply hS i j (y i j-x i j).natAbs; funext u w; by_cases hU:u=i
           swap; simp [advance,W,via,hU]
           subst u; by_cases hw:w=j
           · subst w; simp [advance,W,via,hu,abs_of_nonneg (sub_nonneg.mpr h)]
           simp [advance,W,via,hw]
         apply hS i j (x i j-y i j).natAbs; funext u w; by_cases hU:u=i
         · subst u; by_cases hw:w=j
           · subst w; simp [advance,W,via,hu,abs_of_nonneg (sub_nonneg.mpr h)]
           simp [advance,W,via,hw]
         simp [advance,W,via,hU]
   have h:=hs Finset.univ; rw [show W Finset.univ=x by ext; simp [W,via]] at h; simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,mul_assoc,d] using h

omit ht
variable (S)
def Ink (S:Schedule)(F:ℕ→Tabletop n→ℂ)(N:ℕ)(x:Points n):= F N (Extraction.address (S.a N) x)
lemma tending (F:ℕ→ Tabletop n→ℂ)(h:IsOpen A)(hp:∀ K:Set (Points n), K⊆ A→ IsCompact K→ ∃ b:ℝ,0 ≤ b∧∀ᶠ i in atTop,capping (S.a i) b (F i) K) : Extraction.oscillation A (Ink S F):=by
   intro K hK hk ε he
   obtain ⟨r,hr,hR⟩:= hk.exists_cthickening_subset_open h hK; let V:=cthickening (r/2) K; let Y:=cthickening (r/4) K; obtain ⟨b,hb,hB⟩:=hp (cthickening r K) hR hk.cthickening
   let c:= (n*(4:ℝ)*b); have hc:0≤c:= by unfold c;positivity
   let δ:=min (r/16) (ε/(4*(1+c))); have hδ:0<δ:=lt_min (by positivity) (by positivity)
   have hz : Tendsto (fun i=> (4*n:ℝ)*S.a i) atTop (𝓝 0):= by simpa only [mul_zero] using S.shrinks.const_mul (4*n:ℝ)
   refine ⟨δ,hδ,?_⟩; filter_upwards [hB,hz.eventually_le_const hδ] with i hi hh x hx y hy hD
   let u(x:Points n):= address (S.a i) x; let v x:= tag (S.a i) (u x)
   have hp(x):dist (v x) x≤δ:= (approximate (S.a_pos i) _).trans hh
   have he': dist (v x) (v y) ≤ 3*δ:=by have hv:=dist_triangle4 (v x) x y (v y); rw [dist_comm y] at hv; linarith only [hp x,hp y,hD,hv]
   have hr': 16*δ≤r :=(mul_comm _ _).trans_le ((le_div_iff₀ (by positivity : (0:ℝ)<16)).mp (min_le_left _ _))
   have hu:v y∈ Y:=mem_cthickening_of_dist_le _ _ _ _ hy ((hp y).trans (by linarith only [hr',hδ]))
   have hl : cthickening (2*(3*δ)) Y⊆ cthickening r K:=(cthickening_cthickening_subset (by positivity : 0≤2*(3*δ)) (by positivity : 0≤r/4) K).trans (cthickening_mono (by linarith only [hr',hr]) K)
   have hX:=hop (S.a_pos i) hi hb _ _ hu hl he'; refine lt_of_le_of_lt (hX.trans (mul_le_mul_of_nonneg_left he' hc)) ?_
   · have hv :4*(1+c)*δ≤ε:= (le_div_iff₀' (by positivity)).mp (min_le_right _ _); nlinarith only [hc,hv,hδ,mul_nonneg hc hδ.le]
end oscillatory
end YM.UVExtension.Poppy
