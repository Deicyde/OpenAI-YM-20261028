import YM.Contacts.Harvest.Aperture
import YM.Contacts.Harvest.ReadingToll
/-! # Price totals with subpower reserves across joint/nested collision strata

Reprice at each elected branch in a shell in order to charge smaller nodes and tails. Volume factor
arises here in `‖det A‖`. A pointwise L1 estimate on an eigen-resized parameter may therefore
work uniformly even on shells near proper-stratum collapse. The moment-sum estimate in the final
calculation consumes some of the epsilon reserve at all remaining scales, explicit enough for
simultaneous choices of annuli in all the open groups.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers
open scoped Topology Classical BigOperators ContDiff InnerProductSpace
variable {k : ℕ}{E W I : Type} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
local notation "GN" => Normal.Group k
variable {g : Normal.Group k}{Q : Pieces g}{P:E→ₗᵢ[ℝ] Points k} {d : Fin k→ℕ} {γ ε ε' : ℝ}
namespace Route
variable (r : Route P Q I W) (w : W)(i:Q.parts)

/-- Amount of `ε'` by which we inflate at each step. Later fixed total below 1. -/
def tariff (Q : Pieces g) : ℝ:= (3:ℝ)^(g.card-Q.parts.card)
lemma tariff_one : 1≤ tariff Q:= one_le_pow₀ (by norm_num)
lemma tariff_spent (u : Splittings i.val) : 3*tariff (replace i u.val) ≤ tariff Q:=by unfold tariff; rw [mul_comm,← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by have hh:= replace_finer i u.property; have he:=(replace i u.val).card_parts_le_card; omega)
lemma tariff_first : tariff Q≤3^ (g.card):= pow_le_pow_right₀ (by norm_num) (Nat.sub_le ..)
lemma tariff_less (j : Splittings i.val) : tariff (replace i j.val) ≤ tariff Q:= by linarith only [tariff_spent i j, tariff_one (Q:=replace i j.val)]

def generosity (Q : Pieces g) (γ : ℝ) : ℝ := tariff Q * γ
structure Economy (Q : Pieces g)(γ : ℝ) : Prop where
   pos : 0<γ
   total : generosity Q γ+γ ≤ 1
lemma Economy.inherited (u : Splittings i.val) (h : Economy Q γ) : Economy (replace i u.val) γ:= ⟨h.pos,(add_le_add_left (mul_le_mul_of_nonneg_right (tariff_less i u) h.pos.le) γ).trans h.total⟩
lemma expand (u : Splittings i.val)(hp : 0 < γ) : 2*generosity (replace i u.val) γ+γ ≤ generosity Q γ:= by unfold generosity; linarith only [le_mul_of_one_le_left hp.le (tariff_one (Q:=replace i u.val)),mul_le_mul_of_nonneg_right (tariff_spent i u) hp.le]
lemma generosity_pos (h : 0 < γ) : 0 < generosity Q γ:= mul_pos (zero_lt_one.trans_le tariff_one) h

/-- Sum of input field dimensions. Sign at testing will be negative. -/
def arityRate (d : Fin k→ℕ) (i : Normal.Group k) : ℝ:= (i.sum d : ℕ)
lemma add_arity {Q : Pieces g}(d : Fin k→ℕ) : arityRate d g= Q.parts.sum (arityRate d):= by unfold arityRate; rw [costs_bind Q d,Nat.cast_sum]

def basic (A:E≃L[ℝ] E) := |LinearMap.det A.toLinearEquiv.toLinearMap|
omit [FiniteDimensional ℝ E] in
lemma basic_pos (A:E≃L[ℝ] E): 0< basic A:= abs_pos.mpr (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero -- check
lemma normal_cost {R a : ℝ}{A : E≃L[ℝ] E}{K : Submodule ℝ E} (hr:0<a)(hR:0<R) : basic (relaunch K A a R hr hR) = basic A * (a/R)^(Module.finrank ℝ K):= by
   have he:(relaunch K A a R hr hR).toLinearEquiv.toLinearMap=A.toLinearEquiv.toLinearMap.comp (slide K (a/R)).toLinearMap:= rfl
   unfold basic; rw [he,LinearMap.det_comp,slide_det,abs_mul,abs_of_pos (pow_pos (div_pos hr hR) _)]
lemma adds {a b t:ℝ}(he:0<t) : t^a*t^b=t^(a+b):= (Real.rpow_add he a b).symm
lemma prices_height {φ : Filter ℕ}{T : ℕ→ℝ}{U : ℕ→W}(s : GN→ ℝ) (d : Fin k→ℕ) (hs : ∀ i∈ Q.parts, RateIs φ T (r.R i ∘ U) (-(s i))) (ht : Tendsto T φ atTop) : RateIs φ T (fun i=> ∏ j∈ Q.parts,(r.R j (U i))^(-(arityRate d j))) (Q.parts.sum (fun i=> arityRate d i*s i)):= by
   refine RateIs.prod (fun i hi=> ((hs i hi).rpow (-(arityRate d i))).swap (by ring)) ht -- supply?

/-- Sum result desired at gravity. Fields given fixed norm bounds. -/
def face (d : Fin k→ℕ) (w : W) : ℝ:= ∏ i∈Q.parts,r.R i w^ (-(arityRate d i))
def bag [Fintype I] (d : Fin k→ℕ) (B : W→ℝ)(w : W)(ε : ℝ) := basic (r.frame w)*r.face d w * B w * surcharges r.diameter w ε
lemma face_pos (d : Fin k→ℕ) : 0<r.face d w:= Finset.prod_pos fun i _=> Real.rpow_pos_of_pos (r.valid i _).1 _
lemma bag_pos [Fintype I] (d : Fin k→ℕ){B : W→ℝ} (hm : 0<B w) : 0< r.bag d B w ε:= by have h:=r.face_pos w d; have h':=basic_pos (r.frame w); have he:0 < surcharges r.diameter w ε:= Finset.prod_pos (f:=fun i=>r.diameter i w ^ (-ε)) (fun i hi=> Real.rpow_pos_of_pos (r.accounted i w).1 _); unfold bag; positivity

def kick (f : Menu k)(i : Normal.Group k) (γ : ℝ) := if i.card ≤ 1 then 1 else (f i).slice.elim (1:ℝ) (fun i=> (dyad i)^γ)
def shadow (Q : Pieces g) (f : Menu k)(γ : ℝ) := ∏ i∈Q.parts,kick f i γ
def behind (Q : Pieces g) (i : Q.parts) (f : Menu k)(γ : ℝ) := ∏ j∈ Q.parts.erase i.val, kick f j γ
lemma bare {f : Menu k} {i:GN} (h : (f i).slice=none) : kick f i γ= 1:=by unfold kick; rw [h]; split <;> rfl
lemma paid {f : Menu k} {i:GN} (h:i.card≤1) : kick f i γ=1:=if_pos h
lemma kick_pos (i : GN) (f : Menu k) : 0<kick f i γ:= by unfold kick; cases hs:(f i).slice <;> split; exacts [one_pos,one_pos,one_pos,Real.rpow_pos_of_pos (dyad_pos _) _]
lemma behind_pos (Q : Pieces g) (i : Q.parts)(f : Menu k) : 0 < behind Q i f γ := Finset.prod_pos fun j _=> kick_pos j f
lemma from_behind (f : Menu k) : shadow Q f γ= behind Q i f γ * kick f i.val γ := Eq.symm (Finset.prod_erase_mul _ _ i.property)
lemma cleared {f : Menu k} (h : ∀ i∈Q.parts,(f i).slice=none) : shadow Q f γ=1:= Finset.prod_eq_one fun i hi=> bare (h i hi)

variable (u : Fans P i.val) (v : Splittings i.val) (h : 1 < i.val.card) (b : Way d i.val)
local notation "q" => replace i v.val -- shadow warning
variable (p : r.ramp i (outward b) u v)
lemma inherits_kick (f : Menu k)(ε : ℝ) : shadow (replace i v.val) (widenMenu v f) ε= behind Q i f ε:= by
   unfold shadow; rw [replace_parts, Finset.prod_union (replace_disj i v.val), Finset.prod_eq_one (f:=fun j=> kick (widenMenu v f) j ε) (s:=v.val.parts) (fun j hj=> bare (by rw [menu_small v f hj]; rfl)), mul_one]; exact Finset.prod_congr rfl fun j hj=> by unfold kick; rw [menu_unchanged v f (Finset.disjoint_left.mp (replace_disj i v.val) hj)]
lemma inherit_face : (r.renew i (outward b) u v h).face d p=
     r.face d p.val.1 * (p.val.2 / r.R i.val p.val.1) ^ (-(arityRate d i.val)):= by
   let N:= r.R i.val p.val.1; have hh : 0< p.val.2:= p.property.1.1; have hm : 0<N:= (r.valid ..).1
   let y(j : GN):= (r.renew i (outward b) u v h).R j p ^(-(arityRate d j)); let x (j:GN):=r.R j p.val.1 ^(-(arityRate d j)); change (replace i v.val).parts.prod y= Q.parts.prod x * (p.val.2/N) ^ (-(arityRate d i.val))
   rw [replace_parts, Finset.prod_union (replace_disj i v.val), Finset.prod_congr rfl (s₁:=Q.parts.erase i.val) (f:=y) (g:=x) (fun j hj=>by unfold y x; rw [R_there r i (outward b) u v h (Finset.disjoint_left.mp (replace_disj i v.val) hj) p]),← Finset.prod_erase_mul Q.parts x i.property,mul_assoc]; apply congrArg ((Q.parts.erase i.val).prod x * ·)
   have ht : x i.val*(p.val.2/N) ^(-(arityRate d i.val))=p.val.2^(-(arityRate d i.val)):= by change N^_ *(p.val.2/N)^_=_; rw [← Real.mul_rpow hm.le (div_nonneg hh.le hm.le),mul_div_cancel₀ _ hm.ne']
   rw [ht, add_arity (Q:=v.val) d, ← Finset.sum_neg_distrib,Real.rpow_sum_of_pos hh]; exact Finset.prod_congr rfl fun j hj=>by rw [R_here r i (outward b) u v h hj p]

variable [Fintype I]
lemma pay_piece : surcharges (r.renew i (outward b) u v h).diameter p ε = p.val.2^(-ε)*surcharges r.diameter p.val.1 ε:= by unfold surcharges; rw [Fintype.prod_option]; rfl
lemma fees_pos : 0< surcharges r.diameter w ε:= Finset.prod_pos fun j _=> Real.rpow_pos_of_pos (r.accounted j w).1 _
lemma surcharge_i (j : I) (he : 0 ≤ ε) : (r.diameter j w)^(-ε)≤ surcharges r.diameter w ε:= by let f (j:I):=(r.diameter j w)^(-ε); have hy i : 1 ≤ f i:= Real.one_le_rpow_of_pos_of_le_one_of_nonpos (r.accounted i w).1 (r.accounted i w).2 (neg_nonpos.mpr he); change f j ≤ ∏ j,f j; rw [← Finset.mul_prod_erase (f:=f) Finset.univ (Finset.mem_univ j)]; exact le_mul_of_one_le_right (le_trans zero_le_one (hy j)) (Finset.one_le_prod (fun i _=>hy i))
lemma add_fees : surcharges r.diameter w (γ+ε)= surcharges r.diameter w γ * surcharges r.diameter w ε:= by
   unfold surcharges; simp_rw [neg_add, ← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun j _=> Real.rpow_add (r.accounted j w).1 _ _
lemma fees_mono (he : γ ≤ ε) : surcharges r.diameter w γ ≤ surcharges r.diameter w ε:= Finset.prod_le_prod (fun j _=> (Real.rpow_pos_of_pos (r.accounted j w).1 _).le) (fun j _=> Real.rpow_le_rpow_of_exponent_ge (r.accounted j w).1 (r.accounted j w).2 (neg_le_neg he))
lemma fees_room (h : ε + ε' ≤ γ) (hp : 0 ≤ ε') : surcharges r.diameter w ε * (r.R i.val w)^(-ε') ≤ surcharges r.diameter w γ := calc
   _ ≤ surcharges r.diameter w ε * surcharges r.diameter w ε':=mul_le_mul_of_nonneg_left (r.surcharge_i w (r.register i.val) hp) (r.fees_pos w).le
   _ = surcharges r.diameter w (ε + ε') := (r.add_fees w).symm -- ? specify expr
   _ ≤ _ := r.fees_mono w h
end Route
end YM.Contacts.Harvest
