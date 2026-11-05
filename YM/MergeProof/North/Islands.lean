import YM.MergeProof.North.Corn
import YM.MergeProof.North.Junction
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V
variable {c₀ b b':V}{B:Equiv.Perm V}{E:Equiv.Perm ι}{m:Motion}{x:Site f}{M:ι→Hat (Aged V) R}{π:R.activities.Moves m.1 x}(h:Kin M c₀ b B m x π E) {w:Name V→ℝ}(hw:∀ i:Bool,w (c₀,i)=w (b,i))
namespace Kin
include h hw
lemma fares (i:ι)(he:Focused c₀ (M i).s): sumFee (M (E i)) w=sumFee (M i) w:=by
   simp_rw [sumFee,(h.plot _ he).1,(h.plot _ he).2.2,norm_scalar]; refine congr_arg (·*_) ?_
   unfold Poly.toll; rw [drum,pares, prod_image (nome B).injective.injOn]; refine prod_congr rfl ?_ ; rintro ⟨i,j⟩ hi; have hI : i=c₀:= mem_singleton.mp (he (mem_image_of_mem Prod.fst hi)); rw [hI]; change w (B c₀, _)= _; rw [h.here,hw]; rfl
lemma tenor (i:ι)(he:Focused c₀ (M i).s): Harm c₀ B m (Menu.sing (M i) w) (Menu.sing (M (E i)) w):=by
   unfold Menu.sing; rw [h.fares hw i he,(h.plot i he).1,(h.plot i he).2.2]; convert Harm.solo _ _ using 2
   unfold Motion.scalar; split<;> simp
local notation "F!" => fun i=> Menu.sing (M i) w
lemma riot (f g f' g':Ways ι)(hf:Models f f')(hg:Models g g')(hp:∀ (t:ℝ)(s:Finset ι), (∀ i∈s,Focused c₀ (M i).s) → g t (s.image E)=f t s) : Harm c₀ B m (sound (fun i=>Menu.sing (M i) w) f) (sound (fun i=>Menu.sing (M i) w) g):=by
   intro p hv; unfold sound; simp only [mapScores_apply, Poly.part_sum,Poly.part_smul]
   rw [← scales,← Equiv.sum_comp E.finsetCongr]
   refine sum_congr rfl fun i _=>?_; rw [Equiv.finsetCongr_apply,map_eq_image]; change (jet g (i.image E):ℂ)* (∏ j∈i.image E,(F!) j).part _=scalar m ((jet f i:ℂ)* (∏ j∈i,(F!) j).part _) -- parentheses
   by_cases he : ∀ j∈i,Focused c₀ (M j).s
   · rw [jetTurn hf hg E (fun t _ p ht=> hp t p (fun i hi=> he _ (ht hi))),prod_image E.injective.injOn,(Harm.prod_ i (F!) (fun j=>(F!) (E j)) (fun i hi=> h.tenor hw i (he i hi))) p hv,scalar_mul,scalar_real]
   have hz(v:V)(s:Finset ι)(p:(X).Mode)(hp: Focused v p)(h:¬∀ i∈s, Focused v (M i).s): (∏ j∈s,(F!) j).part p=0:=by
       by_contra h'
       simp only [Menu.sing] at h'
       have hh:Fits (fun i=> (M i).s) s:= fits_of_tagged_prod _ (fun hz=> h' (by rw [hz,Poly.part_nil])); rw [tagged_prod _ s hh,Poly.part_send] at h'; split at h'
       next he=> refine h (fun i hi=>?_) ;exact monoFocus (he.symm ▸ (subset_biUnion_of_mem (fun i=>(M i).s.val) hi : (M i).s.val ⊆ (unionTag _ _ hh).val)) hp
       contradiction
   have ht : ¬ ∀ j∈ i.image E, Focused b (M j).s:= fun hC=> he (fun j hj=> (h.cares j).mpr (hC _ (mem_image_of_mem _ hj)))
   rw [hz _ i _ hv he,hz _ (i.image E) _ (h.here ▸ (going ..).1 hv) ht,mul_zero,mul_zero,scalar_z]
end Kin
end YM.MergeProof.Ribbons
