import YM.Next.SCHEDULE.Stadium
import YM.Planned.PRIMARY_INTEGRAL_295.Density
import YM.Planned.PRIMARY_INTEGRAL_295.Quire
/-!
# Camp across the unforced forecast cone from full template Quantum

Employ genuine d_L of all seats even though turns may read reversed
representatives. Projection/burn of cabin unknown locally; here global
price on unforced extension of tested V chart. All quantities post-L
before realizing actual. No assuming quadratic exterior algebra gauge in
this phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Density
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place
open Villa Fizz Fizz.Gush Bazaars Cedar Quire Oval
open Bunks Little Work.F01 Little.Core
open Progress.StationaryScenes.Green Push.Uniform Floor
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Gauge} {z n k:ℕ} {c f:Side} {S : StepData c f}
variable {K : Core G S} {W:Lines S.ratio.count} {w: Trinket}
namespace Trinket
variable (w) (G:Gauge) (L:Side)
def lease (η:ℝ):= ↑(originN G L) * countCost η
def bow (η:ℝ):= ↑(curlN G L)*countCost η
lemma lease_ge {η:ℝ}(h:0<η):0≤ lease G L η:= mul_nonneg (Nat.cast_nonneg _) (count_pos h).le
lemma bow_ge {η:ℝ}(h:0<η):0≤ bow G L η:= mul_nonneg (Nat.cast_nonneg _) (count_pos h).le

def salary (k:ℕ):= 1+ 2^k*(2*w.C)^2*lease G L (w.α/2)
lemma salary_ge (k:ℕ):1≤ salary w G L k:= by
   have ht:=lease_ge G L (half_pos w.wisdom); unfold salary; apply le_add_of_nonneg_right; positivity

def fullCost (k:ℕ):= 1+salary w G L k * bow G L (w.α/4)
lemma fullCost_ge (k:ℕ):1≤ fullCost w G L k:= by
   have hc:=w.wisdom; have ht:=bow_ge G L (η:=w.α/4) (by positivity); have he:= salary_ge w G L k; unfold fullCost; apply le_add_of_nonneg_right; positivity

def paid (G:Gauge) (L:Side) (k:ℕ):Aim:= by
   let t:=w.start/2; let C:= w.fullCost G L k
   let u:= min 1 ((t/2)/C); have ht:0<t:=half_pos w.health; have he:1≤C:= fullCost_ge ..; have hm:=w.wisdom
   refine ⟨C,t,w.α/4,u,ht,he,⟨by positivity,lt_min one_pos (by positivity),min_le_left ..⟩,(le_div_iff₀ (show 0<C by positivity)).mp (min_le_right ..)⟩
lemma paidα (k:ℕ): (w.paid G L k).starry ≤ w.α/4:= by
   have he := w.wisdom; unfold Aim.starry; rw [show (w.paid G L k).σ=w.α/4 from rfl]
   exact mul_le_of_le_one_left (by positivity) (w.paid G L k).wave.2.2

def tone (k:ℕ) (M t:ℝ):= w.C*t*(M+flake k M)
def race (k:ℕ)(M t:ℝ):= 3*2^k*w.C*w.tone k M t* lease G L (w.α/2)
lemma tone_ge (k:ℕ){M t:ℝ}(hM:0≤M)(ht:0≤t):0≤w.tone k M t:=by have hc:= w.witness; unfold tone flake; positivity
lemma race_ge (k:ℕ){M t:ℝ}(hM:0≤M)(ht:0≤t):0≤w.race G L k M t:=by
    have hc:=w.witness; have he:=lease_ge G L (half_pos w.wisdom); have hi:= tone_ge w k hM ht; unfold race; positivity
end Trinket
open Trinket
variable {t M:ℝ} {b:E→Dir G c}
section Curve
abbrev stepped (K:Core G S) (b:E→Dir G c) (t:ℝ) (x:E) := K.Gram (t • b x)
structure Guide (b:E→Dir G c) (t M:ℝ) (K:Core G S) (w:Trinket) (W:Lines S.ratio.count) (k:ℕ) : Prop where
  price : Quantum K w W k
  plate : t∈Ioc 0 1 ∧ t*M ≤ w.radius
  position : Ember k b M
  quarts : w.tone k M t ≤ w.C
  burns : w.race G S.ratio.count k M t * bow G S.ratio.count (w.α/2) ≤ w.start/2

namespace Guide
variable (h : Guide b t M K w W k)
include h
-- path around b authority
lemma lintel (i:Seats G c f) (j:Acres f G):
     let g:= fun y:E=> K.D (t • b y) i j; let q : E→ℝ:= fun _=> K.D 0 i j; let z:=Decay w.α (origin S i) (chair S j)
     Ember k q (w.C*z) ∧ Ember k g (2*w.C*z) ∧ Ember k (g-q) (w.tone k M t*z) := by
   intro g q z
   have hm:=h.position.2.1; have he:= decay_pos w.α (origin S i) (chair S j)
   have hC := h.price.drums i j _ (show ‖(0:Dir G c)‖≤w.radius by rw [norm_zero]; exact w.rprice)
   have hf:Ember k q (w.C*z):=Ember.weakening (Ember.constant (q 0) _) hC.value
   have hw : Ember k (g-q) (w.tone k M t*z):=by
       have hz:=Quire.lived (h.price.drums i j) w.rprice h.plate.1 h.position h.plate.2
       rw [show w.C*z*t*(M+flake k M)=w.tone k M t*z from by unfold Trinket.tone; ring] at hz; exact hz
   refine ⟨hf,?_,hw⟩
   rw [show g=q+(g-q) from by abel]; refine Ember.weakening (Ember.join hf hw) ?_; have hx:=h.quarts; nlinarith [mul_le_mul_of_nonneg_right hx he.le]

omit h in
private lemma issued {S:StepData c f}{K:Core G S}(i j:Acres f G): |K.fires i j| ≤ Decay (w.α/2) (chair S i) (chair S j) := by
   by_cases ht:i=j
   · subst i; unfold Little.Core.fires; rw [Matrix.diagonal_apply_eq]; split <;> simp [Decay]
   unfold Little.Core.fires; rw [Matrix.diagonal_apply,if_neg ht,abs_zero]; exact (decay_pos ..).le

lemma mountains (i j:Acres f G) :
    let α:=w.α; let l:=chair (G:=G) S; let r:=Decay (α/2) (l i) (l j); let f(x:E):=(stepped K b t x) i j
    Ember k f (w.salary G S.ratio.count k*r) ∧ Ember k (fun x=> f x-K.Gram 0 i j) (w.race G S.ratio.count k M t*r) := by
   intro α l r F₀
   let x0(u:Seats G c _) (i:Acres f G):= Decay α (origin S u) (l i)
   let d(u:Seats G c _) (i:Acres f G):= fun x:E=> K.D (t • b x) u i
   let d'(u:Seats G c _) (i:Acres f G):= fun _:E=> K.D 0 u i
   let v:= w.C; let q:=w.tone k M t; let a:=2^k*(2*v)^2; let u:=3*2^k*v*q
   have he:= half_pos w.wisdom; have hh(p:Seats G c _)(i:Acres f G) : 0 ≤ x0 p i:=(decay_pos ..).le
   have ht:0 ≤ q:= tone_ge _ _ h.position.2.1 h.plate.1.1.le
   have hx:= w.witness
   have hZ:1≤v:=hx; have ha :0≤a:=by unfold a; positivity
   have hu :0≤u:=by unfold u; positivity
   let f'(p:Seats G c _) (x:E):= d p i x*d p j x
   let g(p:Seats G c _) (x:E):= f' p x-d' p i x*d' p j x
   let F(p:Seats G c _):=x0 p i*x0 p j
   have hp (p:Seats G c _) : Ember k (f' p) (a*F p) ∧ Ember k (g p) (u*F p):=by
     obtain ⟨hv,hI,hU⟩:= h.lintel p i; obtain ⟨hv',hI',hU'⟩:= h.lintel p j
     constructor
     · have hz:= Ember.fires hI hI'; rw [show 2^k*(2*v*x0 p i*(2*v*x0 p j))=a*F p from by unfold a F; ring] at hz; exact hz
     have hz:= Ember.join (Ember.fires hU hI') (Ember.fires hv hU')
     have hR := show 2^k*(q*x0 p i*(2*v*x0 p j))+2^k*(v*x0 p i*(q*x0 p j))=u*F p from by unfold u F; ring
     rw [hR] at hz
     apply Ember.renamed hz; filter_upwards with x; change d p i x*d p j x-d' p i x*d' p j x=(d p i x-d' p i x)*d p j x+d' p i x*(d p j x-d' p j x); ring
   let D:=lease G S.ratio.count (w.α/2)
   have hb : ∑ p, F p ≤ D*r:= haul (origin_count G S) w.wisdom ..
   have hr M (hm:0≤M): ∑ p, M*F p ≤ M*D*r := by rw [←Finset.mul_sum,mul_assoc]; exact mul_le_mul_of_nonneg_left hb hm
   have hF:= Ember.weakening (Ember.total Finset.univ _ f' (fun p _=>(hp p).1)) (hr a ha)
   have hI : Ember k (fun _ : E=>K.fires i j) r:= Ember.weakening (Ember.constant ..) (issued (S:=S) (w:=w) ..)
   constructor
   · apply Ember.weakening (show Ember k F₀ (a*D*r+r) from Ember.join hF hI); change a*D*r+r ≤ (1+a*D)*r; apply le_of_eq; ring
   have hG := Ember.weakening (Ember.total Finset.univ _ g (fun p _=>(hp p).2)) (hr u hu)
   apply Ember.renamed (show Ember k _ (w.race G S.ratio.count k M t * r) from hG)
   filter_upwards with x
   change (∑ p,f' p x)+ K.fires _ _ -((∑ p,d' p i x*d' p j x)+_)=_
   unfold g; rw [Finset.sum_sub_distrib]; abel

lemma at_oracle : let c':= S.ratio.count; let l := chair (G:=G) S; let q:=w.paid G c' k; let f:=stepped K b t
    q.Camp (f 0) l ∧ Vault q l f k (w.salary G c' k) := by
  intro c' l q f; have hJ:= chair_count G S
  let D := w.race G c' k M t; let B:= w.salary G c' k; let L:= w.α/2
  have hh:0≤D:= w.race_ge G c' _ h.position.2.1 h.plate.1.1.le
  have he:1≤B:= w.salary_ge G c' k; have hL : 0<L:=half_pos w.wisdom
  have hc (i:Acres _ G): (∑ j, D*Decay L (l i) (l j)) ≤ w.start/2 := by rw [←Finset.mul_sum]; apply le_trans _ h.burns; apply mul_le_mul_of_nonneg_left (hJ.count l hL _) hh
  let P:=K.Gram 0; let Δ:= P-f 0
  have hH(i j): |Δ i j|≤ D*Decay L (l i) (l j) := by
      have ht := (h.mountains i j).2.2.value; change |f 0 i j-P i j| ≤ _ at ht; change |P i j-f 0 i j|≤_; rwa [abs_sub_comm]
  have hx: Bottom (f 0) (w.start/2):=by
     intro v
     have he:= Progress.StationaryScenes.Green.schur Δ v (w.start/2) (fun i=> (Finset.sum_le_sum (fun j _=>hH i j)).trans (hc i)) (fun i=> ?_)
     · unfold Δ at he; rw [Matrix.sub_mulVec,dotProduct_sub] at he; have ht:= h.price.root v; linarith [le_abs_self _|>.trans he]
     apply le_trans (Finset.sum_le_sum (fun j _=> hH j i)); simp_rw [decay_comm _ _ (l i)]; exact hc i
  have hX := K.sym (t • b 0)
  let r := w.α/4
  have hv : Progress.StationaryScenes.Green.Rows l l (f 0) r q.C := by
      intro i; apply (Finset.sum_le_sum (g:=fun j=> Progress.StationaryScenes.Green.wt r (l i) (l j)*(B*Decay L (l j) (l i))) ?_).trans
      · simp_rw [← mul_assoc,mul_comm _ B, mul_assoc,←Finset.mul_sum]
        have hz:L-r=w.α/4:=by unfold L r; ring
        have ht:=weight_budget (show r<L by unfold r L; linarith [w.wisdom]) hJ (l i); rw [hz] at ht
        exact (mul_le_mul_of_nonneg_left ht (zero_le_one.trans he)).trans (le_add_of_nonneg_left zero_le_one)
      intro j _; refine mul_le_mul_of_nonneg_left ?_ (wt_pos ..).le; rw [decay_comm L]; exact (h.mountains i j).1.2.value
  have hz : (f 0).transpose=f 0:=by ext i j; exact hX.apply i j
  refine ⟨⟨hx,hX,hv,?col⟩,fun i j=>?_⟩
  · rw [hz]; exact hv
  apply Ember.weakening (h.mountains i j).1; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans he)
  apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_right _ (by positivity); have hb:=w.paidα G c' k; unfold q; linarith [w.wisdom]
end Guide
end Curve
end YM.Planned.PrimaryIntegral295.Density
