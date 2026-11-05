import YM.MergeProof.Cashew
import YM.MergeProof.Paddle

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent PhysicalNext.Repeat.Lotus Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{d:ℕ}(H:History G) (A:Hol G){F:Labels.Frame G d}(T:SectionData F)
   (W:Bid.Worth)(ζ u ψ:ℕ→ℝ)(t:ℝ)(i k N p:ℕ) (M:Extra.Histories.Music F H N p)
set_option quotPrecheck false
variable (V:F.Coeff)(a:Motion)(o:∀ m:ℕ, Site (H.S.side m p))(w:ℕ→ℝ)
   (f:∀ m:ℕ,Config G (H.S.side m p)→ℂ)(g:∀ m:ℕ,ℕ → Config G (H.S.side m p)→ℂ)(b:Config G (H.S.side N p)→ℂ)(D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
open Relay
section knobs
-- increase φ bill optional after L. no ε.
lemma diet (H:History G)(d k:ℕ)(η ρ:ℕ→ℝ)(w :ℝ)(hp:0<w)(hh: ∀ i,k ≤ i → 0 < η i)
    (hx:∀ i,k ≤ i → η i *((H.S.block i).val:ℝ)^(d+1)*ρ i ≤ ρ (i+1)) (m:ℕ) (E:ℝ)(hb:0≤E)
    (hv:w*‖alto H k d‖*(E/gainChart H m k) ≤ ρ k): ∀ i:ℕ,k ≤ i→ (march (fun _:Unit=>w) η k i ())*‖alto H i d‖*(E/gainChart H m i) ≤ ρ i := by
   have he(i):0 < gainChart H m i:=Real.exp_pos _
   have heq(i):gainChart H m i=gainChart H m (i+1)*puffs (H.S.block i):=by unfold gainChart puffs; rw [H.S.scale_succ,Real.rpow_def_of_pos (by positivity),← Real.exp_add]; congr 1; ring
   have ht(i):0 < puffs (H.S.block i):=by unfold puffs; positivity
   let s (i):= march (fun _:Unit=>w) η k i (); have hs (i:ℕ)(hi:k ≤ i):0 < s i:=by induction hi with
                                                                                     | refl=>unfold s; rw [marines k η _ (fun _=>hp)]; exact hp
                                                                                     | step he ih=>unfold s; rw [march,if_pos (show k ≤ _ from he)]; exact mul_pos (hh _ he) ih
   intro i hi; change s i *_*_ ≤ _
   induction hi with
   | refl=> unfold s; rw [marines k η _ (fun _=>hp)]; exact hv
   | step hi ih=> rename_i i
                  let L:= H.S.block i; let v:=s i; let x:= ‖alto H i d‖; let a:=E/gainChart H m i; let q:=puffs L
                  have hl : (1:ℝ) ≤ L.val:= by exact_mod_cast L.property
                  have hf: q≤L.val:= by unfold q puffs; exact Real.rpow_le_self_of_one_le hl (by norm_num)
                  have hv:0≤a:= div_nonneg hb (he i).le
                  rw [show s (i+1)=η i*s i from by unfold s; rw [march,if_pos (show k ≤ _ from hi)], show ‖alto H (i+1) d‖= (↑L.val:ℝ)^d*x by rw [alto_at,norm_mul,norm_pow,Complex.norm_natCast],show E/gainChart H m (i+1)= q*a from by unfold a q L; rw [heq i]; have hT:= ht i; have hz:=he (i+1); field_simp]
                  apply le_trans _ (hx i hi)
                  exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf hv) (mul_nonneg (mul_nonneg (hh _ hi).le (hs _ hi|>.le)) (mul_nonneg (pow_nonneg (zero_le_one.trans hl) _) (norm_nonneg _)))) ((le_of_eq (b:=η i *((H.S.block i).val:ℝ)^(d+1)*(s i*x*a)) (by unfold L; ring)).trans (mul_le_mul_of_nonneg_left ih (mul_nonneg (hh _ hi).le (by positivity))))
end knobs
section
lemma Attainment.plus {n:Side}{P:BudgetPoint}{o:Site n}{f g:MergeProof.Response G n}{t s:ℝ}(h:Attainment P o f t)(hx:Attainment P o g s): Attainment P o (f+g) (t+s):=by
   have hv (i:Bool):Attainment P o (twain f g i) (twain t s i):=by cases i; exact hx; exact h
   have he:= perform hv Summable.of_finite|>.1; rw [tsum_fintype,Fintype.sum_bool,show band (twain f g)=(f+g) from funext fun i=> funext fun U=>by unfold band;rw [tsum_fintype,Fintype.sum_bool]; rfl] at he; exact he
lemma hook_add {n:Side}{f g:MergeProof.Response G n}{X:Activities G n}{t:ℝ}:hook X t (f+g)=hook X t f+hook X t g:=by funext i U; simp only [hook,Pi.add_apply,add_mul,Finset.sum_add_distrib]
end
end YM.MergeProof
