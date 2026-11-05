import YM.FullVolume.Mark.Sight
/-! Insertion step is FULL Lipschitz on canonical graphs. Dimensionless contraction estimates survive even for the unit. No Θ replanning. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{B:SectionData F}{H:History G} {N p m:ℕ} {Y:Hol G}
set_option quotPrecheck false
local notation "A₀"=>H.rep N p m
local notation "A₁"=>H.rep N p (m+1)
local notation "s₀"=> H.S.side (m+1) p
local notation "s₁"=> H.S.side m p
local notation "Z"=> orbitCost F
local notation "μ"=>kappa H m
local notation "μ'"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
local notation "s"=> (H.levels.params (m+1)).columns
local notation "s'"=> (H.levels.params m).columns
variable {S:Desk G (H.S.side (m+1) p)}{E:Desk G (H.S.side m p)}
variable (P:Tool F H N p m){D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}{W:Worth}{T:Heading F}{c ε v t:ℝ}{X:Set Wing}
variable (hx:P.Cap B Y W D T c ε v X)(h:Well (H.rep N p (m+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (m+1))))
variable (Q U : Gram F Y S ((H.levels.params (m+1)).columns))(ha:Afford P.plate Y (H.rep N p (m+1)) (H.rep N p m))
local notation "T₁"=> P.portfolio Q.scythe
local notation "T₂"=> P.portfolio U.scythe
lemma equalityS (i:Tally F) : (T₁ i).support=(T₂ i).support:= turn_same (P.shot i.2 (Coin.uses _)) _ _ _ rfl -- edit
include hx h ha
lemma buyers (i:Tally F): let q:= Q.g (Size.axis F i.2); let r:= U.g (Size.axis F i.2)
    let a:= breakP (P.portfolio Q.scythe i) (P.portfolio U.scythe i);let A:= ε * ‖q-r‖
    a.Format 0 Y A₀ ∧ F.coeffSize a.x ≤ A∧a.remBound 0 A₀ μ A:=by
    intro q r A₁' V; have hv:= socket P hx h i.2 q r ha; let b:= breakP (P.shot i.2 (Coin.uses q)) (P.shot i.2 (Coin.uses r))
    have hP:A₁'= audition (P.whirl i.1) b:= (turn_br ..).symm; rw [hP]
    obtain ⟨f,g,hf,hTz⟩:= hv.income
    obtain ⟨he,hk,hU,-⟩:= audition_receipt i.1 (P.whirl i.1) ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S m p)) hx.good hv.earns hf
    exact ⟨hk,(he.symm ▸ ((patch_cost ..).trans hv.first) : _),hU.bound hTz⟩
variable (hp : roomCost H.levels W)(hk:Bank W H.levels) (hu:Well (H.rep N p m) E (Real.sqrt (H.levels.clock.forcedAllowance m)))
include hp hk hu
-- norms budget BOTH. operator norm of F.Coeff→Arena measured in F.coeffSize.
namespace Gram
def Within {n:Side}{F:Labels.Frame G d}{S:Desk G n}{r:ℝ}(Q U:Gram F Y S r)(a:ℝ): Prop:=0≤a∧∀ v, ‖Q.g v-U.g v‖ ≤ a*r*F.coeffSize v
local notation "Q'"=> Q.index P hx h hp hk
local notation "U'"=> U.index P hx h hp hk
local notation "R₁"=> Q.recorded P hx h hu hp hk
local notation "R₂"=> U.recorded P hx h hu hp hk
local notation "V₁"=> Q.step P hx h hu hp hk
local notation "V₂"=> U.step P hx h hu hp hk
lemma communes (hv: Q.Within U t)(x:F.Coeff) : F.coeffSize (Q.index P hx h hp hk x - U.index P hx h hp hk x) ≤ ε*(t*s)* Z * F.coeffSize x ∧ ‖R₁ x- R₂ x‖ ≤ ε*(t*s)* Z * F.coeffSize x:=by
     let b:= ε*(t*s)* Z
     let Y1:= Q.point P; let Y2:=U.point P; let p':= breakP (Y1 x) (Y2 x)
     let f(i:Tally F):=breakP (T₁ i) (T₂ i); let A(i:Tally F):= ε*‖Q.g (Size.axis F i.2)-U.g (Size.axis F i.2)‖; let g(i:Tally F):=chips F x i
     have hf(i):= buyers P hx h Q U ha i; have ht:= hx.budget.epsilon; have hs:= hv.1; have hM:s≥0:= zero_le_one.trans (H.levels.params (m+1)).columns_ge
     have hε:∑ i:Tally F,‖g i‖ * A i ≤ b * F.coeffSize x:=by
        have hy i: A i ≤ ε*(t*s):=(mul_le_mul_of_nonneg_left (hv.2 _) ht).trans_eq (by rw [Size.size_axis,mul_one])
        refine (sum_le_sum (fun i _=> mul_le_mul_of_nonneg_left (hy i) (norm_nonneg (g i)))).trans ?_
        rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right (rip F x) (mul_nonneg ht (mul_nonneg hs hM))).trans_eq (by unfold b; ring)
     have he : p' = Extra.Histories.pencil (code _) f (chips F) x:= (pencil_br ..).symm
     refine ⟨?_ ,?_⟩
     · change F.coeffSize p'.x ≤ b*_; rw [he,pencil_x]
       apply (Size.finite F _ _).trans ((sum_le_sum ?_).trans hε); intro i _; rw [Size.smul]; exact mul_le_mul_of_nonneg_left (hf i).2.1 (norm_nonneg _)
     have hx':(Y1 x).support=(Y2 x).support:=by
        funext i; exact congr_fun (equalityS P Q U (code (Tally F) i).1) (code _ i).2
     have hf' : Coin.uses (R₁ x- R₂ x)= capture p' P.down:=by rw [map_sub]; exact (collected _ _ _ hx' (Q.prose P hx h hp hk x).2.1 (U.prose P hx h hp hk x).2.1).symm
     apply (Coin.wealths _).mpr; rw [hf']; rw [he]
     obtain ⟨hz,hr⟩:= pencil_cost (code _) f (chips F) (Real.sqrt_pos.mpr (forcedPos ..)) (fun i=> ⟨(hf i).1,(hf i).2.2⟩) x; exact alongPay hu _ _ hz (rem_mono hr hε)
section numerical
omit hu ha h hp in
lemma bank0 : 0 ≤ barunit (H.S.block m) ∧ 4 * s * barunit (H.S.block m) ≤ 1:=by
     let A:= puffs (H.S.block m); let S₂:= s; let W':= W.K (H.levels.clock.J (m+1)+1); have he:1≤S₂:= (H.levels.params (m+1)).columns_ge
     have hy :1 ≤ W'^6:=one_le_pow₀ (W.prices _); have hz:S₂ ≤ (1+S₂)^2:=by nlinarith only [he]
     have hm : 4*S₂ ≤ A:= le_trans (b:=100000*W'^6*(1+S₂)^2) (mul_le_mul (by linarith only [hy]) hz (zero_le_one.trans he) (by linarith only [hy])) (hk m)
     have hA: 1≤A:=by linarith
     change 0≤A⁻¹^3∧ 4*S₂*A⁻¹^3≤1; refine ⟨by positivity,?_⟩; rw [inv_pow,← div_eq_mul_inv]; exact (div_le_one₀ (by positivity)).mpr (hm.trans (by simpa only [pow_one] using (pow_le_pow_right₀ hA (show 1 ≤ 3 by omega)))) -- rw issue
end numerical
lemma revenue (hv: Q.Within U t): (Q.step P hx h hu hp hk).Within (U.step P hx h hu hp hk) (t/2):=by
    refine ⟨div_nonneg hv.1 (by norm_num),fun x=>?_⟩; let y:= (Q').symm x; let a:=(U') y
    have hr: x=Q' y:= ((Q').apply_symm_apply _).symm
    let b:= ε*(t*s)*Z; have ht₁:(V₁).g x=(R₁) y:= by
       conv_lhs=> rw [hr]
       exact signs ..
    have ht₂ : (V₂).g a=(R₂) y:= signs ..
    have hx' : F.coeffSize y ≤ s* F.coeffSize x:=by rw [hr]; exact (Q.prose P hx h hp hk y|>.2.2)
    obtain ⟨hv₀,hv₁⟩:= Q.communes P hx h U ha hp hk hu hv y
    have hΔ : F.coeffSize (a-x) ≤ b *F.coeffSize y := (Work.G08.size_sub_rev ..).trans_le (by nth_rw 1 [hr]; exact hv₀)
    have hs:s≥1:=(H.levels.params (m+1)).columns_ge; have hs':s'≥1:=(H.levels.params m).columns_ge
    have hz: Z≥1:= orbitCost_one_le F; have hε:=hx.budget.epsilon; have ht:= hv.1
    have he: ε*s*Z≤ barunit (H.S.block m):= ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hε) (zero_le_one.trans hz))).trans hx.budget.tiny
    have hb: b*s ≤ t/4:=by
        unfold b; rw [show ε*(t*s)*Z*s=t*(ε*s*Z*s) from by ring]
        refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (zero_le_one.trans hs)) ht).trans ?_
        have h':= bank0 P hx hk|>.2; have h:barunit (H.S.block m)*s ≤ 1/4:=by linarith only [h']
        exact (mul_le_mul_of_nonneg_left h ht).trans_eq (by ring)
    have hV : b*F.coeffSize y ≤ t/4*F.coeffSize x:= ((mul_le_mul_of_nonneg_left hx' (by unfold b; positivity)).trans ((mul_assoc ..).symm.le)).trans (mul_le_mul_of_nonneg_right hb (Work.G08.size_nonneg ..))
    have hF: ‖R₂ y - (V₂).g x‖ ≤ s'*(t/4*F.coeffSize x):=by rw [←ht₂,← map_sub]; exact ((V₂).toll _).trans (mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans (hΔ.trans hV)) (zero_le_one.trans hs'))
    change ‖(V₁).g x- (V₂).g x‖ ≤ _; rw [ht₁,show R₁ y- _= (R₁ y-R₂ y)+(R₂ y- (V₂).g x) by abel]
    apply (norm_add_le ..).trans; apply (add_le_add (hv₁.trans (hV.trans (le_mul_of_one_le_left (mul_nonneg (by positivity) (Work.G08.size_nonneg ..)) hs'))) hF).trans
    apply le_of_eq; ring
end Gram
end YM.MergeProof.Matric
