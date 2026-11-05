import YM.MergeProof.North.Tan
import YM.MergeProof.South.Sight
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
lemma stair_eq (φ:ℕ→ℝ)(w:ℝ)(m i:ℕ) : stair φ w m i=w*stair φ 1 m i:=by
    induction i with
    | zero=> change w=w*1; exact (mul_one ..).symm
    | succ i ih=> by_cases hp:m ≤ i; simp only [stair,march,if_pos hp]; change φ i*stair φ w m i=w*(φ i*stair φ 1 m i); rw [ih,mul_left_comm]; simp only [stair,march,if_neg hp, mul_one]
lemma stair_cost (φ:ℕ→ℝ)(v x:ℝ)(a:ℂ)(m i:ℕ)(hx:0 < x) : stair φ v m i*‖a‖=(v*‖a‖/x)*stair φ x m i:=by
    rw [stair_eq φ v, stair_eq φ x]; field_simp
section
variable {I:Type}[Fintype I](h:Scrim C W u ψ φ δ ζ r D)
variable {o:∀ i,Site (C.side i p)}{x:I→ℝ}(a:I→ℂ){F':I→∀ i:ℕ,Config G (C.side i p)→ℂ}{K:I→∀ i:ℕ,ℕ → Config G (C.side i p)→ℂ}
   (hk:m≤k)(e:k≤N)(hw:0<w)(hx:∀ i,0 < x i)(hz:∑ i,w*‖a i‖/x i≤1)
local notation "t!"=> stair φ
local notation "f"=> fun j=>∑ i,(a i • F' i j)
local notation "Z"=> fun j=>∑ i,(a i • K i j)
include H e h hw hx hz
lemma rearranged (hh:∀ i,Wakes T m k N p o (t! (x i) m) (F' i) (K i) D e)(hc:∀ i j,m ≤ j→ j≤k→ Integrable (coin (R j) (F' i j) (K i j)) (prior G _)) : Wakes T m k N p o (t! w m) (f) (Z) D e:=by
    have hJ(i j)(hp : m ≤ j)(hv : j≤k): Dominated (a i • K i j):=rainbow ((hh i).stocked j hp hv) _; let Y:=f; let Z':=Z
    refine ⟨fun i he h=> combies _ (fun j=> hJ j i he h) _,fun j hj hv=> ?_,fun i hK hm=>?_⟩
    · choose μ y b c ht he hα hf using fun i=> (hh i).sways j hj hv
      let A:=⋃ i,μ i; let B:= Fintype.card I; let β i:=a i*y i
      let b' i:=‖a i‖*b i; let c' i:=‖a i‖*c i; have hη(i):0≤ b i ∧ 0 ≤ c i:=by
         obtain ⟨L,y1,M,s,ψ,hx⟩:=hf i; obtain ⟨e,H,p⟩:=hx.cost.toll
         exact ⟨sumBudget_credit hx.purchase,sumBudget_credit H⟩
      have hg(i):0 ≤ b' i:=mul_nonneg (norm_nonneg _) (hη i).1; have hγ(i):0≤ c' i:=mul_nonneg (norm_nonneg _) (hη i).2
      let u':= t! w m (j+1); let τ' i:= t! (x i) m (j+1); let pX i:= w*‖a i‖/x i; have hp i:0 ≤ pX i:=div_nonneg (mul_nonneg hw.le (norm_nonneg _)) (hx i).le
      refine ⟨A,∑ i,β i,∑ i,b' i,∑ i,c' i,Set.finite_iUnion ht,?_,?_,?_⟩
      · rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show 2*u'*b' i≤pX i from ?_)) hz
        rw [show 2*u'*b' i=pX i*(2*τ' i*b i) from by unfold b'; have hE:u'*‖a i‖=pX i*τ' i:= stair_cost _ _ _ _ _ _ (hx i); calc
                   _= 2*(u'*‖a i‖)*b i:= by ring
                   _= _:= by rw [hE];ring]; exact mul_le_of_le_one_right (hp i) (he i)
      · rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show u'*c' i≤ pX i from ?_)) hz
        unfold u' c'; rw [← mul_assoc, stair_cost _ _ _ _ _ _ (hx i),mul_assoc]; exact mul_le_of_le_one_right (hp i) (hα i)
      obtain ⟨v,β₁,hQ,H⟩:=h.costs.night.days N p j (hv.trans_le e)
      change Tale A _ _ _ (∑ i,a i • F' i (j+1)) (profile _ (∑ i,a i • K i (j+1))) (profile _ (∑ i,a i • K i j)) _ _ _ _
      -- elem
      simp_rw [prof_sum _ (fun i=> hJ i (j+1) (hj.trans j.le_succ) hv), prof_sum _ (fun i=>hJ i j hj hv.le),profile_scale]; apply Tale.upon hQ.propagate (fun i=> ((hf i).travel (a i)).climb (Set.subset_iUnion μ i) le_rfl le_rfl) _ _ _ (hasSum_fintype β) ⟨hg,Summable.of_finite,(tsum_fintype ..).le⟩ ⟨hγ,Summable.of_finite,(tsum_fintype ..).le⟩
      · intro i; rw [Finset.sum_apply]; exact hasSum_fintype _
      · intro i U; rw [Finset.sum_apply, Finset.sum_apply]; exact hasSum_fintype _
      intro i U; rw [Finset.sum_apply,Finset.sum_apply]; exact hasSum_fintype _
    let H':= hm.trans_le e; have hR:= (H.wilson.represents  N p (i+1) H').good.labels; have hR₀:= (H.wilson.represents N p i H'.le).good.labels
    simp_rw [coin_sum _ _ (fun j=>hJ j i hK hm.le) _ hR₀.boundK, coin_sum _ _ (fun j=> hJ j (i+1) (hK.trans i.le_succ) hm) _ hR.boundK,coin_mul,push_list _ (fun j=>(hc j (i+1) (hK.trans i.le_succ) hm).smul (a j)) _ (T|>.levels.transition_mass ..)]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [(hh j).feeds i hK hm, StepData.push_smul _ _ _ _ (hc j _ (hK.trans i.le_succ) hm)]
end
end YM.MergeProof
