import YM.Further.SHELL_BIRTH_49.Fusing.Coal
import YM.MergeProof.Fleece
import YM.MergeProof.North.Blade
import YM.MergeProof.Sonata

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory
open scoped Topology BigOperators Classical
variable {ι:Type}{G:Gauge}{N d n p m:ℕ}(H:History G)(B:SectionData ((Labels.frames G).level d))
local notation "Z"=> H.rep N p (m+1)
local notation "K"=> H.rep N p m
local notation "s"=> (H.S.side (m+1) p)
open Float Planned.GuardedAtom Motion
set_option quotPrecheck false
variable (A:Source.Hol G) {x y z a:ℝ}{f:Config G (H.S.side (m+1) p)→ℂ} {g:Res G (H.S.side (m+1) p)} {u:Config G (H.S.side (m+1) p)→ℂ} {Q:Set Wing}{D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
lemma stamped {L:Side}{P:Coefficient ((Labels.frames G).level n) L} {R:Rep G L}(h:Tab P 0 R x y z)(c:ℂ): Tab (Extra.Histories.stretch c P) 0 R x (‖c‖*y) (‖c‖*z):=by
   obtain ⟨e,he,ht⟩:= h.regular; obtain ⟨f,hf,hy⟩:=h.forced
   refine ⟨h.divisor,mul_nonneg (norm_nonneg _) h.first,mul_nonneg (norm_nonneg _) h.second, ⟨fun i=> ‖c‖*e i,?_,fun i=> Next.Foundations.bound_smul c (ht i)⟩,fun i=> ‖c‖ *f i,?_,fun i=>⟨mul_nonneg (norm_nonneg _) (hy i).1,fun U=> ?_⟩⟩
   · simp_rw [mass_scale];exact Extra.Histories.budget_scale he (norm_nonneg _)
   · simp_rw [mass_scale,mul_left_comm x ‖c‖ z]; exact Extra.Histories.budget_scale hf (norm_nonneg _)
   rw [show (Extra.Histories.stretch c P).forced i U=c • P.forced i U from rfl,norm_smul]; exact mul_le_mul_of_nonneg_left ((hy i).2 U) (norm_nonneg _)
lemma thorough (h: Coupon B H N p m A f g 0 D Q u 0 x x y)(c:ℂ)(hp:Integrable u (prior G _)): Coupon B H N p m A (c • f) (c • g) 0 D Q (c • u) 0 (‖c‖*x) (‖c‖*x) (‖c‖*y):=by
   obtain ⟨P,hP,h⟩:=h; let U:= Extra.Histories.stretch c P
   refine ⟨U,⟨stretch_format _ hP.format,?_,?_,?_⟩,?_⟩
   · have hx:U.density 0 B K = c • P.density 0 B K :=by funext i; exact stretch_density ..
     rw [hx,hP.agrees]; unfold Extra.Histories.blast; rw [StepData.push_smul _ _ _ _ hp,smul_smul,smul_smul,mul_comm c]
   · have he:= hP.leadP; rw [sub_zero] at he; rw [sub_zero]; rw [show U.x=c • P.x from rfl,Size.smul,mul_left_comm _ ‖c‖ _]; exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
   · obtain ⟨b,t,hf,ht⟩:=hP.future; refine ⟨_,_,stamped hf c,?_⟩; rw [mul_left_comm _ ‖c‖ _,← mul_add]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg c)
   have he:= h.travel c; rw [mul_zero,← profile_scale] at he; exact he

def Throws (H:History G)(N p m:ℕ)(D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(A:Source.Hol G) (B:SectionData ((Labels.frames G).level d)) (x:ℝ): Prop:=∀ (q:Set Wing)(M: Lotus.Leaf (H.rep N p (m+1))),M.turn∈q → 0∈ M.crest → Coupon B H N p m A (prose M) (entry M) 0 D q (Complex.ofReal ∘ M.cicada) 0 (x* load M) (x* load M) (2*load M)
lemma tossing {k:ℕ→ Config G (H.S.side (m+1) p)→ℂ}(h:Blade (Z) 0 f (profile (Z).activities k) 0 a)(ht: Dominated k)(hx:H.Selected)(hm:m<N)(hp:0 ≤ x)(he:SoundDoor (H.levels.clock.op m p) D)(hv:Throws H N p m D A B x):∃ q:Set Wing,q.Finite ∧ Coupon B H N p m A f (profile (Z).activities k) 0 D q (coin (Z) f k) 0 (x*a) (x*a) (2*a):=by
    obtain ⟨I,i,M,r,h⟩:=h; have hy:= hx.represents N p (m+1) hm
    let Q:Set Wing:= Set.range fun i=> (M i).turn; let g(i):= r i • (Complex.ofReal ∘ (M i).cicada); let z i:=‖r i‖*(x*load (M i)); let v := (Z).p
    have hr i:=thorough H B A (hv Q (M i) ⟨i,rfl⟩ (h.sit i)) (r i) ((M i|>.sells hy.good).1.integrable _).ofReal
    refine ⟨Q,Set.finite_range _,?_⟩; rw [h.display hy.good.labels ht,zero_smul, zero_add]
    cases isEmpty_or_nonempty I; swap
    · have Hq i:= (Leaf.sells (M i) hy.good).1
      have ht': Dominated g:=by
         choose y hx using fun i=> (Hq i).2; refine ⟨fun i=>‖r i‖*y i,Summable.of_finite,fun i U=>?_⟩; unfold g; simp only [Pi.smul_apply,norm_smul,Complex.norm_real,comp_apply]; exact mul_le_mul_of_nonneg_left (hx i _) (norm_nonneg _)
      let x₂ i:= r i • prose (M i); let y i:= r i • entry (M i); have hs: f= ∑ i,x₂ i:=h.lit.trans (zero_add _)
      have hk:= coupons B H _ _ _ A D he hx hm.le (f:=g) hr (φ:=f) (ψ:=profile (Z).activities k) (fun U=>by rw [hs]; simp only [Finset.sum_apply, ← show ∀ i, x₂ i=r i • prose (M i) from fun _=>rfl]; exact hasSum_fintype _) (fun j U=> by rw [h.run]; simp only [Finset.sum_apply]; exact hasSum_fintype _) hasSum_zero ht' (fun i=> (Complex.continuous_ofReal.measurable.comp (Hq i).1).const_smul _) (Summable.of_finite) (Summable.of_finite) (Summable.of_finite) (Summable.of_finite)
      have hf : (fun V=> ∑' i,g i V)= ∑ i,g i:=by funext U;simp_rw [tsum_fintype,Finset.sum_apply]
      rw [hf,tsum_zero] at hk
      have hv': ∑' i,z i ≤ x*a:=by unfold z; simp_rw [tsum_fintype,mul_left_comm _ x _, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h.pay hp
      have he: ∑' i, ‖r i‖*(2*load (M i)) ≤ 2*a:=by simp_rw [tsum_fintype,mul_left_comm _ (2:ℝ) (load _), ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h.pay zero_le_two
      exact hk.weaken hv' hv' he
    have hE:0 ≤ a:=by simpa using h.pay
    rw [h.lit, h.run]; simp_rw [Finset.sum_of_isEmpty]; rw [add_zero]; exact zeroSlot B H N p m A Q D hx (mul_nonneg hp hE) (mul_nonneg zero_le_two hE)
end YM.MergeProof
