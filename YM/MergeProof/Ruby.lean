import YM.MergeProof.Alpaca
import YM.MergeProof.Crisp
import YM.MergeProof.Domino
/-! Price at the TRUE top k (strong) of transfer. Exponent+2. No loss on transported jobs. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories Ac Bid Local
open Planned.GuardedAtom Accent PhysicalNext.Repeat.Lotus Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{d:ℕ} (H:History G) (A:Hol G){F:Labels.Frame G d}(T:SectionData F)
   (W:Bid.Worth)(ζ u ψ:ℕ→ℝ)(t:ℝ)(k N p:ℕ) (M:Extra.Histories.Music F H N p)
set_option quotPrecheck false
local notation "K"=> H.levels
local notation "P"=> H.levels.budget
local notation "Γ"=> (fun m=>(H.levels.params m).columns)
local notation "R"=> H.rep N p
local notation "Gx"=> M.tone
local notation "n!"=> H.S.side N p
local notation "X"=> alto H
variable (V: F.Coeff)(r:ℝ)
local notation "T!"=> T.footprint (0:Site (H.S.side N p))
private lemma shave (a:F.Coeff): F.coeffSize (F.core a) ≤ F.coeffSize a:= by unfold Labels.Frame.coeffSize; apply sum_le_sum; intro j _; change ‖Function.update a 0 0 j‖≤_; by_cases h:j=0 <;>simp [h]
lemma erected {hT:T.Sound A} (hb:∀ (i:F.Index)(U:Config G (H.S.side N p)), ‖T.places (Size.axis F i) 0 U‖ ≤ t) (hx:H.Selected)(h: Sung T H N p A W k M)(hw:r*bond H N p M N V≤ζ N) (hv:Banks H F t u ζ N) (hc: coverNumber (P N).B T! ≤ 1)(hr:0 ≤ r) : ∃ g, Attainment (R N).p 0 (booster T (R N) 0 V) g ∧ r*(‖X N d‖*g) ≤ u N:=by
    let f:= fullCost F (P N) t; let a:= f*F.coeffSize (F.core V); let Z:= R N; let p':= Z.p; have hp: (R N).p= P N:=(hx.represents N p N le_rfl).vac; let g:=Real.exp (p'.supportExponent+2)*a
    have hP:F.coeffSize (F.core V)≤F.coeffSize ((M.tone N).index V):=by rw [← h.head.heard.currents,h.head.out]; exact shave V
    have hq:0 ≤ f:=by unfold f fullCost; have ht:0≤t:=zero_le_one.trans hv.cost; have he:=(P N).threshold_pos; positivity
    have hh:0 ≤ a:=mul_nonneg hq (Work.G08.size_nonneg ..); refine ⟨g,?_,?_⟩
    · have hC (i:Support n!): 0 ≤ (Pi.single T! a: Support n! → ℝ) i:=by by_cases h:i=T!; rw [h,Pi.single_eq_same]; exact hh; rw [Pi.single_eq_of_ne h]
      refine ⟨fun i=>?_,fun i hi=>?_,Pi.single T! a,⟨fun i=>mul_nonneg (Real.exp_pos _).le (hC i),Summable.of_finite,?_⟩,fun i=>⟨hC i,fun U=>?_⟩⟩
      · unfold booster; by_cases h:i=T!; rw [h,Pi.single_eq_same]; exact ⟨supplement_read T (R N) 0 V,supplement_gauge _ _ _ hT _,supplement_meas _ _ _ _,healthy_supplement _ _ _ hT _⟩
        rw [Pi.single_eq_of_ne h]; exact Local.Attaches.zero ..
      · have he : i=T!:= not_not.mp (fun h=>hi (Pi.single_eq_of_ne h _)); rw [he]; exact Finset.mem_image.mpr ⟨0,hT.anchored,by simp⟩
      · rw [tsum_fintype,Finset.sum_eq_single T!,Pi.single_eq_same]; unfold reservedMass; apply mul_le_mul_of_nonneg_right ?_ hh
        · rw [hp]; apply Real.exp_monotone; have ht : (coverNumber (P N).B T! : ℝ) ≤ 1:= by exact_mod_cast hc
          change _ ≤ (R N).p.supportExponent+2; rw [hp]; exact mul_le_of_le_one_right (by linarith only [(P N).exponent_pos]) ht
        · intro i _ hi; rw [Pi.single_eq_of_ne hi,reservedMass,mul_zero]
        simp
      unfold booster; by_cases h':i=T!; rw [h',Pi.single_eq_same,Pi.single_eq_same]; have he := supplement_bound T (R N) 0 hT hv.cost hb V U; rw [hp] at he; exact he
      rw [Pi.single_eq_of_ne h',Pi.single_eq_of_ne h']; simp
    unfold g a; change _*(‖alto ..‖*(Real.exp ((R N).p.supportExponent+2)*_)) ≤ _
    rw [hp]; let x:=Real.exp ((P N).supportExponent+2)*f; refine le_trans (le_of_eq (b:=x*(r*(‖alto H N d‖*F.coeffSize (F.core V)))) (by unfold x; ring)) (le_trans ?_ hv.candle)
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (norm_nonneg _)) hr).trans hw) (mul_nonneg (Real.exp_pos _).le hq)
variable (m:Motion)(b:Site (H.S.side N p))
lemma mural (hv:OnTop T H N p A (Gx N))(h:H.Selected) (U) : ((R N).eval U:ℂ)*(stepUp m b (initial T H N p V 0) U)=radiant (X N d) m b (((Gx N).plays V).density 0 T (R N)) U:=by
   change liftVac H N p N _ * Motion.scalar m _=alto H N d* Motion.scalar m _
   rw [hv.earns, show ((↑((R N).eval (pull m.1 b U)):ℂ))= _ from vac_pull H N p N h le_rfl m.1 b U]
   let X0:ℂ:=(H.S.a N:ℂ)^d; have he:X0≠0:=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (H.S.a_pos N).ne'); simp_rw [Motion.scalar_mul]
   rw [show Motion.scalar m X0=X0 from by unfold Motion.scalar X0;split_ifs <;>simp,show Motion.scalar m (liftVac H N p N U)=liftVac H N p N U from Motion.scalar_real ..,mul_assoc X0,show alto H N d=X0⁻¹ from rfl,inv_mul_cancel_left₀ he]
end YM.MergeProof
