import YM.MergeProof.Hens
import YM.MergeProof.Memo

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Accent Push Local Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{f c:Side}{ι V:Type*}{d:ℕ}{F:Labels.Frame G d}{T:SectionData F}{o:Site f}
   {P:Coefficient F f}{R:Rep G f}{E:Rep G c}{A:Hol G}(m:Motion) (x: Site f) (π:R.activities.Moves m.1 x)
-- offset
lemma audition_turn (hn:2 ≤ f.val)(ht:T.Sound A)(hf:P.Format o A R){κ a b:ℝ} (h:Tab P o R κ a b) : let p:=audition π P; let s:=affine m.1 x o;p.Format s A R∧ Tab p s R κ (turnCost R.p.order R.p.power*a) b ∧ p.density s T R=stepUp m x (P.density o T R):=by
   intro p s; have hx:= format_reorient π hf hn; have he:= Tab.turn π h hf; have hz:=density_reorient (o:=o) π ht P
   unfold p audition stepUp Motion.scalar; cases m.2 with
   | false=> exact ⟨hx,he,hz⟩
   | true => exact ⟨format_barAll hx, he.bar hx,(density_barAll _ ht).trans (congr_arg star hz)⟩
lemma nickel_mul (A:Activities G f)(t:BudgetPoint)(y:Finset ℕ)(U:Config G f)(F:ℕ→ℂ)(v:ℂ): Accent.nickel t A y U (v • F)= v* Accent.nickel t A y U F:=by unfold Accent.nickel;split_ifs; simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]; exact (mul_zero _).symm
lemma coin_mul (R:Rep G f)(F:Config G f→ℂ)(K:ℕ → Config G f→ℂ)(v:ℂ): coin R (v • F) (v • K)=v • coin R F K:=by
   funext U
   unfold coin;change ((R.eval U:ℝ):ℂ)*(v*F U)+(Real.exp (R.exponent U):ℂ)*(∑' i,nickel R.p R.activities i U (v • (fun j=> K j U)))=v*(((R.eval U:ℝ):ℂ)*F U + (Real.exp (R.exponent U):ℂ)*∑' i,nickel R.p R.activities i U (fun j=> K j U))
   simp_rw [nickel_mul,tsum_mul_left]; ring
variable {X:PhysicalNext.Repeat.Lotus.Wing→Prop} {b:Site c}{v δ:ℂ}{α:Config G f→ℂ}{ωs:Res G f}{β:Res G c}{t u a w:ℝ}{H:GaugeDoor R E}
-- reweight physical
lemma Tale.pitch (h:Tale X o b v α ωs β δ t u H) (z s:ℂ)(he:z=v*s):Tale X o b 1 (z • α) (z • ωs) (s • β) (z*δ) (‖z‖*t) (‖s‖*u) H:=by
   obtain ⟨ι,hp,M,c,q,hx⟩:= h
   have hr:= hx.quaver z; refine Odyssey.tale (M:=M) (ψ:=s • q) (s:=z • c) ⟨hr.member,hr.purchase,stack_of hx.cost s,hr.lyric,hr.old,fun j U=>?_⟩
   simp only [hook_scale,one_mul,Pi.smul_apply,smul_eq_mul, ← mul_sub,he]
   exact ((hx.grants j U).mul_left s).congr_fun fun i=> by ring
-- scalar pull in push
section
variable (A:History G) (k N p d:ℕ)
local notation "f" => A.S.side (k+1) p
local notation "c"=> A.S.side k p
local notation "S"=> (A.levels.clock.op k p)
local notation "β"=> A.β N p (k+1)
variable (b: Site (A.S.side k p)) (F:Config G (A.S.side (k+1) p) →ℂ)(h:Integrable F (prior G _))
include h
lemma unison : blast A N p k d (stepUp m ((S).ratio.embed b) F)= stepUp m b (blast A N p k d F):=by
   have he : (S).push β (stepUp m ((S).ratio.embed b) F) = stepUp m b ((S).push β F) := by
     funext V
     have he := push_pull A k p β m.1 b F h V
     dsimp only at he
     cases m with
     | mk s z=>
       cases z
       · exact he
       change (S).push β (fun U=> star (F (pull s ((S).ratio.embed b) U))) V= star ((S).push β F (pull s b V)); change (S).push β _ V=(S).push β F (pull s b V) at he
       rw [← he]; unfold StepData.push; let L:= starL' ℝ (A:=ℂ)
       simp_rw [← show ∀ (r:ℝ)(z:ℂ), star (r • z)=r • star z from fun r z=> by rw [star_smul,star_trivial]]; exact L.integral_comp_comm _
   unfold blast; rw [he]; funext U; simp only [Pi.smul_apply,stepUp,smul_eq_mul,scalar_mul]; unfold Motion.scalar;split_ifs <;> simp
omit h
-- inverse normalization term
def alto : ℂ:=((A.S.a k:ℂ)^d)⁻¹
lemma alto_norm : ‖alto A k d‖= ((A.S.a k)^d)⁻¹:= by have ht:= A.S.a_pos k; simp [alto,Real.norm_of_nonneg ht.le]
lemma alto_at : alto A (k+1) d= ((A.S.block k).val:ℂ)^d*alto A k d:=by unfold alto; rw [A.S.a_step, Complex.ofReal_div, Complex.ofReal_natCast,div_pow,inv_div,div_eq_mul_inv]
lemma lept {x:ℂ} : Motion.scalar m (alto A k d*x)=alto A k d*Motion.scalar m x:=by rw [scalar_mul]; unfold Motion.scalar; split_ifs <;> simp [alto]

end
end YM.MergeProof
