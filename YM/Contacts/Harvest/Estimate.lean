import YM.Contacts.Harvest.Totals
/-!
# Kernel reserve and absolute shell comparison

For each arity point and chosen input grades (basis labels stay fixed;
changes of basis extend linearly), `live` residue reaches carrying at least a full
power gain (before any epsilon charge), projection instead carries that field weight
but Taylor difference still pays **one** in the near-shell range after splitting.
In a far shell only projection or a comparably near residue; absorb this term paying
a ratio-free summable power coming from stage epsilon charges.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest.Route
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers
open scoped Topology Classical BigOperators ContDiff InnerProductSpace
variable {k : ℕ}{E W I : Type} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {g l : Normal.Group k}{Q : Pieces g}{P:E→ₗᵢ[ℝ] Points k}
variable {d : Fin k→ℕ} {γ ε ε' t : ℝ}
local notation "GN" => Normal.Group k
-- current shell scaling factor after integrating lower blocks, before Taylor
abbrev effective {d : Fin k→ℕ}{i : Normal.Group k}(v : Way d i) : ℝ:= (System.relative i:ℝ) + gain v-arityRate d i
lemma extra_live (d : Fin k→ℕ)(i : GN) : 1 ≤ effective (none:Way d i):= by
   unfold effective arityRate; rw [gain_live, levels]
   have he : 1+i.sum d ≤ System.relative i+(i.sum d +1-System.relative i):= by omega
   rw [le_sub_iff_add_le]; exact_mod_cast he
lemma named_projection {v : Fin (levels d l)} : effective (d:=d) (i:=l) (some v) + ((levels d l-1-v.val:ℕ):ℝ) = 0:= by
   have he:v.val<levels d l := v.isLt; unfold effective arityRate; rw [gain_project]; have hh : System.relative l+v.val+(levels d l-1-v.val)=l.sum d := by unfold levels at he ⊢; omega
   rw [← Nat.cast_add]; have hk:(↑(System.relative l+v.val):ℝ)+((levels d l-1-v.val:ℕ):ℝ) = ((l.sum d:ℕ):ℝ):=by exact_mod_cast hh
   linarith only [hk]
lemma outset (v : Way d l)(he : 0<t) (hh:t≤1) : t^(effective v)*tailPay v t≤t:=by
   cases v with
   | none=>
      rw [show tailPay (l:=l) (d:=d) none t=1 from rfl,mul_one]; nth_rw 2 [← Real.rpow_one t]; exact Real.rpow_le_rpow_of_exponent_ge he hh (extra_live ..)
   | some v=>
      unfold tailPay; rw [Option.elim_some,vanishFactor,if_pos hh]; rw [← Real.rpow_natCast, ← Real.rpow_add he, Nat.cast_add,Nat.cast_one,← add_assoc,named_projection (l:=l) (v:=v),zero_add,Real.rpow_one] -- check
lemma far_lit {v : Fin (levels d l)} (he : 1<t) : t^(effective (d:=d) (i:=l) (some v))*tailPay (d:=d) (l:=l) (some v) t=1:=by
   unfold tailPay; rw [Option.elim_some,vanishFactor,if_neg he.not_ge, ← Real.rpow_natCast,← Real.rpow_add (lt_trans zero_lt_one he),named_projection, Real.rpow_zero]

variable (r : Route P Q I W)(i : Q.parts)(u : Fans P i.val)(v : Splittings i.val)(b : Way d i.val)
variable (h : Economy Q γ)(he : 1 < i.val.card)

/- Pay ratio and absolute losses simultaneously. -/
def marginFactor := max 1 ((2*r.reserve)^ (effective (none:Way d i.val))) -- d implicit must resolve
lemma margin_pos : 1≤ r.marginFactor i (d:=d):= le_max_left ..
lemma ratio (p : r.ramp i (outward b) u v) {t : ℝ} (ht : 0≤ t)(ht':t≤1) :
    let a:= p.val.2/r.R i.val p.val.1; a^effective b * tailPay b a ≤ r.marginFactor i (d:=d) * a^t:= by
   dsimp only; let B:=p.val.1; have hp:=p.property.1; have he:=r.valid i.val B; let a:= p.val.2/r.R i.val p.val.1; have ha:0<a:= div_pos hp.1 he.1
   by_cases h':a≤1
   · refine ((outset b ha h').trans ( (?_ : a ≤ a^t))).trans (le_mul_of_one_le_left (Real.rpow_pos_of_pos ha t).le (r.margin_pos i)) -- needs i
     conv_lhs=> rw [← Real.rpow_one a]
     exact Real.rpow_le_rpow_of_exponent_ge ha h' ht'
   have hk:1 ≤ a^t:= Real.one_le_rpow (not_le.mp h'|>.le) ht
   have hs: (p.val.2/r.R i.val p.val.1)^effective b * tailPay b a ≤ r.marginFactor i (d:=d):= by
      -- eliminate v while keeping dependant ramp scale data by passing h when outward false
      suffices hl : outward b=false → a ≤2*r.reserve by
         have hy (g : Way d i.val) (he :outward g=false → a ≤ 2*r.reserve) : a^effective g * tailPay g a ≤ r.marginFactor i (d:=d):= by
           cases g with
           | some v=> rw [far_lit (not_le.mp h')]; exact r.margin_pos i
           | none=> rw [show tailPay (d:=d) (l:=i.val) none a=1 from rfl,mul_one]; exact le_trans (Real.rpow_le_rpow ha.le (he rfl) (zero_le_one.trans (extra_live d i.val))) (le_max_right ..)
         exact hy b hl
      intro h; apply (div_le_iff₀ he.1).2; apply r.active i u v; exact (_root_.Eq.mp (congrArg (fun t => (r.site i t u v p.val.1 p.val.2).Nonempty) h) p.property.2)
   exact hs.trans (le_mul_of_one_le_right (zero_le_one.trans (margin_pos r i)) hk)

-- absorb shell surcharge at exponent ε before multiplying by others
lemma compressed {γ ε B a : ℝ}(hB:0<B)(ha:0<a): (a/B)^(γ+ε)*a^(-ε) = a^γ * B^ (-(γ+ε)) := by
   rw [Real.div_rpow ha.le hB.le, Real.rpow_neg hB.le,div_eq_mul_inv,mul_right_comm _ _ (a^(-ε)),adds ha,add_neg_cancel_right]

-- root relative determinant & exponent equation
variable [Fintype I]
lemma at_parent (B : W→ℝ)(p : r.ramp i (outward b) u v): (r.renew i (outward b) u v he).bag d (r.promise i b u v B) p ε = r.bag d B p.val.1 ε * (p.val.2 / r.R i.val p.val.1) ^ effective b * p.val.2^(-ε):= by
   let a:=p.val.2/r.R i.val p.val.1; let v':=r.renew i (outward b) u v he; let I':= v'.frame p; let U := basic (r.frame p.val.1); let X:= r.face d p.val.1; let C:= B p.val.1; have ha:0<a:= div_pos p.property.1.1 (r.valid ..).1
   have hv : basic I'=U*a^ (System.relative i.val:ℝ) := by
      rw [← show Module.finrank ℝ (normalOn P i.val)= System.relative i.val from dimension_normal (Q.nonempty_of_mem_parts i.property) (r.displaysNormals i.val i.property), Real.rpow_natCast]; exact normal_cost p.property.1.1 (r.valid ..).1
   let S:=surcharges r.diameter p.val.1 ε; let t:= p.val.2 ^ (-ε)
   unfold bag; rw [pay_piece, inherit_face]; change basic I'*(X*a^(-arityRate d i.val)) * (C*a^(gain b:ℝ)) * (t*S)= U*X*C*S*a^effective b * t; unfold effective; rw [hv, sub_eq_add_neg, Real.rpow_add ha, Real.rpow_add ha]; ring

include h
lemma seat {B : W→ℝ}(hB : ∀ w, 0<B w) (p : r.ramp i (outward b) u v) (f : Menu k):
    let a:= p.val.2/r.R i.val p.val.1;
    (r.renew i (outward b) u v he).bag d (r.promise i b u v B) p (generosity (replace i v.val) γ) * shadow (replace i v.val) (widenMenu v f) γ * tailPay b a ≤
       marginFactor r i (d:=d) * r.bag d B p.val.1 (generosity Q γ)* p.val.2 ^ γ * behind Q i f γ:= by
   dsimp only; rw [inherits_kick, at_parent] -- include u? implicit?
   let ε:=generosity (replace i v.val) γ; let ε':= generosity Q γ; let s:=p.val.2; let w:=p.val.1; let a:=s/r.R i.val w
   let g:=marginFactor r i (d:=d); let X:=basic (r.frame w)*r.face d w*B w; let Y:=behind Q i f γ
   have hp:= generosity_pos (Q:=replace i v.val) h.pos; have he1 : γ+ε ≤1:= by rw [add_comm]; exact (h.inherited i v).total
   have ht : surcharges r.diameter w ε * r.R i.val w^(-(γ+ε)) ≤ surcharges r.diameter w ε':= r.fees_room w i (by linarith only [expand i v h.pos]) (le_of_lt (add_pos h.pos hp))
   have hZ : 0 < s:= p.property.1.1; have hx:0<X:= mul_pos (mul_pos (basic_pos _) (r.face_pos w d)) (hB w); have hg:0<g:= zero_lt_one.trans_le (r.margin_pos i); have hY:0<Y:= behind_pos Q i f; have hf:0<surcharges r.diameter w ε:=fees_pos r w
   let QF:=surcharges r.diameter w ε; let QG:=surcharges r.diameter w ε'
   change X* QF * a^effective b * s^(-ε) * Y * tailPay b a ≤ g*(X*QG)*s^γ*Y
   calc
      _ = X * QF * Y * ( (a^effective b * tailPay b a)*s^(-ε)):= by ring
      _ ≤ X* QF * Y * ((g*a^(γ+ε))*s^(-ε)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (r.ratio i u v b p (add_pos h.pos hp).le he1) (by positivity)) (show 0≤ X*QF*Y from mul_nonneg (mul_nonneg hx.le hf.le) hY.le)
      _ = g*(X*(QF*r.R i.val w ^ (-(γ+ε))))*s^γ*Y:= by rw [mul_assoc g, show a^(γ+ε)* s^(-ε)= _ from compressed (r.valid ..).1 hZ]; ring -- metas
      _ ≤ _ := by gcongr
end YM.Contacts.Harvest.Route
