import YM.MergeProof.North.Papyrus
import YM.MergeProof.North.Wings
import YM.MergeProof.North.Wiring
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Ac Extra.Multi Corona Push GridApprox.Nil
namespace Salt
variable (Z:Salt V G n)(w:Name V→ℝ)(t α g η :ℝ)(l m k:ℕ)(hw:∀ i,0<w i)(h:Occupancy Z.grain l)(hg:∀ i,w i*‖Z.pepper i‖ ≤ g)(hm:0<m)
variable (hp:0<η)(hy:η≤1)(hh:∀ i:V, coverNumber m ({Z.focus i,Z.grain (i,true)}:Support n)≤ k)
def scent (s l:ℕ) (α g η a b:ℝ):= (1+l)*η*(l*g*Real.exp α + a)+(1+l)*η*(l*g*Real.exp α + a)+(1+l)*b -- unused s ok
local notation "K"=> Z.vessel t
local notation "W"=> tow w α η k
include hw h hg hm hp hy hh
lemma rate (a b:ℝ)(hg':0≤ g)(ht:Towed w id Z.air m α a)(hV:Towed w Prod.fst Z.river m α b)(ha:0 ≤ α): (K).Rated (tow w α η k) m α (scent m l α g η a b):=by
    have h0:Occupancy Z.focus l:=by
       intro y; let p:=univ.filter fun i=> Z.focus i=y
       have he:p.image (fun i=>(i,false))⊆ univ.filter (fun i=>Z.grain i=y):=by
          intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
       exact le_trans (ge_of_eq (Finset.card_image_of_injective p (fun _ _ h=>Prod.mk.inj h|>.1))) ((card_le_card he).trans (h y))
    let v₀:=l*g*Real.exp α+a; let v₁:=(1+l)*η*v₀
    obtain ⟨v,hv,hX,hE⟩:= Z.paperRate w α g _ m hw h hg hm a hg' ht ha
    let K' i:= Poly.toll W (Z.marker i)*v i; have hz i:0≤K' i:=mul_nonneg (Poly.worth (towP w _ _ _ hw hp) _).le (hv _)
    have he i:=(Z.sits i).2; have hv' : Hit (fun i=>Z.kiln (Z.leaf i) (Z.marker i)) m K' α v₁:=by
       apply Z.hitB _ _ l Z.marker Z.leaf he h0 _ _ _ _ hz hp.le (tsum_nonneg (hE 0).1 |>.trans (hE 0).2.2) hE
       intro i; have Ht : η^(Z.marker i).val.card ≤ η:= by simpa only [pow_one] using pow_le_pow_of_le_one hp.le hy (show 1≤ _ from card_pos.mpr (Z.sits i).1)
       have hu:= Z.levels w α η k m Z.marker Z.leaf he hh ha hp hy hw i
       unfold K'
       have hf:= mul_le_mul_of_nonneg_right (hu.trans (mul_le_mul_of_nonneg_right Ht (mul_nonneg (Real.exp_pos _).le (Poly.worth hw _).le))) (hv i)
       nlinarith only [hf]
    obtain ⟨F,hF,hz',hB⟩:= diced _ Prod.fst w α b m hw hV
    let f:= fun i:Z.Brook=> Poly.toll W i.val.2*F i.val; let A(i:Z.Brook):= i.val.2; let X(i:Z.Brook):= i.val.1.1
    have hf i:0 ≤ f i:=mul_nonneg (Poly.worth (towP _ _ _ _ hw hp) _).le (hF _)
    have ht:(Hit X m (fun i=>Poly.toll w (A i) * F i.val) α b):= fun i=> Budget.pull_le (q:=Subtype.val) (p:=fun _=>True) (hB i) (fun j: Z.Brook=> (hB i).1 j.val) (fun _ _=>trivial) Subtype.val_injective.injOn (fun i _=> le_rfl)
    have hq (i: Z.Brook): (A i).val.image Z.grain ⊆ X i:= i.property.2
    have hu: Hit (fun i:Z.Brook=> Z.kiln (X i) (A i)) m f α ((1+l)*1*b):=by
       apply Z.hitB _ _ _ _ _ hq h0 _ _ 1 b hf zero_le_one (tsum_nonneg (ht 0).1|>.trans (ht 0).2.2) ht
       intro i; have he:=Z.levels w α η k m A X hq hh ha hp hy hw i
       have ht:η^(A i).val.card ≤ 1:=pow_le_one₀ hp.le hy
       change Poly.toll W (A i)* F i.val* Real.exp _ ≤ _; nlinarith only [mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_right ht (mul_nonneg (Real.exp_pos _).le (Poly.worth hw _).le))) (hF i.val)]
    refine ⟨Sum.elim (fun i:Z.Seed=>v i.1) (fun i:Z.Brook=>F i.val),fun i=>?_,fun i U=>?_,fun i=>?_⟩
    · cases i; exact hv _; exact hF _
    · cases i
      next i=> change ‖Z.bud t U i‖ ≤ _; unfold Salt.bud; split; exact hX ..; rw [norm_zero]; exact hv _
      next i=> exact hz' ..
    let f':= fun j:Z.Seed⊕ Z.Brook=> if i∈(K).cover j then (Poly.toll W ((K).mode_ j) * j.elim (fun i:Z.Seed=>v i.1) (fun i:Z.Brook=>F i.val))*Real.exp (α*coverNumber m ((K).cover j)) else 0
    change SumBudget f' _; refine ⟨fun j=>?_,Summable.of_finite,?_⟩
    · cases j
      next j=> exact (hv' i).1 j.1
      next j=> exact (hu i).1 j
    rw [tsum_fintype,Fintype.sum_sum_type]; unfold scent
    refine add_le_add ?_ (le_trans (Budget.cap (hu i) univ) (by simp))
    change ∑ j:Z.Lawn×Bool, f' (Sum.inl j) ≤ v₁+v₁; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_bool]; rw [sum_add_distrib]
    exact add_le_add (Budget.cap (hv' i) univ) (Budget.cap (hv' i) univ)
end Salt
end YM.MergeProof.Ribbons
