import YM.MergeProof.North.Palate
import YM.OPE.Grouping.Wiring
import YM.OPE.Grouping.Shift
import YM.OPE.Grouping.Papyrus
/-!
# Repricing for fibers

Adapting `Palate`. Pay the sibling number in radius with stronger version of `hitB`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {S₀ : Type*} [Fintype S₀] [DecidableEq S₀] {Δ : Fibers S₀ V}
open Ac Extra.Multi Corona Push GridApprox.Nil
namespace Salt
variable (Z:Salt V S₀ Δ G n)(w:S₀→ℝ)(t α g η :ℝ)(l m k:ℕ)(hw:∀ i,0<w i)(h:Occupancy Z.grain l)(hg:∀ i,w i*‖Z.pepper i‖ ≤ g)(hm : 0 < m)
variable (hp:0<η)(hy:η≤1)(hh:∀ i:S₀, coverNumber m ({Z.focus (Δ.bunch i),Z.grain i}:Support n)≤ k)
local notation "K"=> Z.vessel t
variable (c : ℕ) (h_c : 0 < c) (h_f : ∀ i : V,(Δ.contents i).card ≤ c)
local notation "W" => tow w α (η/c) k
include hw hp hy hh
lemma spreadBound {D : Type*} (ha : 0 ≤ α) (p : D → (Bud S₀).Mode) (Y : D → Support n) (q : D → ℝ)
        (hq : ∀ i, 0 ≤ q i) (hY : ∀ i, (p i).val.image Z.grain ⊆ Y i)
        (r : ℝ) (i : D) (hr : η^(p i).val.card ≤ r) :
        Poly.toll (tow w α η k) (p i) * q i * Real.exp (α*coverNumber m (Z.kiln (Y i) (p i))) ≤
          r*(Poly.toll w (p i) * q i * Real.exp (α*coverNumber m (Y i))) := by
       have H := Z.levels w α η k m p Y hY hh ha hp hy hw i
       linarith only [mul_le_mul_of_nonneg_right (H.trans
         (mul_le_mul_of_nonneg_right hr (mul_nonneg (Real.exp_nonneg _) (Poly.worth hw _).le))) (hq i)]

include h_c h_f h hg hm
set_option maxHeartbeats 800000 in
lemma rate (a b:ℝ)(hg':0≤ g)(ht:Towed w id Z.air m α a)(hV:Towed w Prod.fst Z.river m α b)(ha:0 ≤ α): (K).Rated (tow w α (η/c) k) m α (YM.MergeProof.Ribbons.Salt.scent m l α g η a b):=by
    have hc : (0:ℝ)<c:=by exact_mod_cast h_c
    have hp' : 0 < η/c:= by positivity
    have hα : η/c ≤ η := div_le_self hp.le (by exact_mod_cast h_c : (1:ℝ) ≤ c)
    have hy' := hα.trans hy
    have h0:Occupancy Z.focus l:=by
       intro y; let p:=univ.filter fun i=> Z.focus i=y
       have he:p.image Δ.twig⊆ univ.filter (fun i=>Z.grain i=y):=by
          intro i hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
       exact le_trans (ge_of_eq (Finset.card_image_of_injective p  Δ.sectioned.injective)) ((card_le_card he).trans (h y))
    let v₀:=l*g*Real.exp α+a; let v₁:=(1+l)*η*v₀
    obtain ⟨v,hv,hX,hE⟩:= Z.paperRate w α g _ m hw h hg hm a hg' ht ha
    let K' i:= Poly.toll W (Z.marker i)*v i; have hz i:0≤K' i:=mul_nonneg (Poly.worth (towP w _ _ _ hw hp') _).le (hv _)
    have he i:=(Z.sits i).2
    have shr (p:(Bud S₀).Mode) (h:p.val.Nonempty): (η/c)^p.val.card ≤ η/c := by
       simpa only [pow_one] using pow_le_pow_of_le_one hp'.le hy' (show 1≤ _ from card_pos.mpr h)
    have hv' : Hit (fun i=>Z.kiln (Z.leaf i) (Z.marker i)) m K' α v₁ :=
       Z.hitB _ _ l Z.marker Z.leaf he h0 _ _ _ _ hz hp.le (tsum_nonneg (hE 0).1 |>.trans (hE 0).2.2) hE c h_c h_f
          (fun i => Z.spreadBound w α (η/c) m k hw hp' hy' hh ha Z.marker Z.leaf v hv he _ i ((shr _ (Z.sits i).1).trans hα))
          (fun i hj => Z.spreadBound w α (η/c) m k hw hp' hy' hh ha Z.marker Z.leaf v hv he _ i (shr _ hj))
    obtain ⟨F,hF,hz',hB⟩:= YM.MergeProof.Ribbons.Salt.diced _ Prod.fst w α b m hw hV
    let f:= fun i:Z.Brook=> Poly.toll W i.val.2*F i.val; let A(i:Z.Brook):= i.val.2; let X(i:Z.Brook):= i.val.1.1
    have hf i:0 ≤ f i:=mul_nonneg (Poly.worth (towP _ _ _ _ hw hp') _).le (hF _)
    have ht:(Hit X m (fun i=>Poly.toll w (A i) * F i.val) α b):= fun i=> Budget.pull_le (q:=Subtype.val) (p:=fun _=>True) (hB i) (fun j: Z.Brook=> (hB i).1 j.val) (fun _ _=>trivial) Subtype.val_injective.injOn (fun i _=> le_rfl)
    have hq (i: Z.Brook): (A i).val.image Z.grain ⊆ X i:= i.property.2
    have hu: Hit (fun i:Z.Brook=> Z.kiln (X i) (A i)) m f α ((1+l)*1*b):=
       Z.hitB _ _ _ _ _ hq h0 _ _ 1 b hf zero_le_one (tsum_nonneg (ht 0).1|>.trans (ht 0).2.2)
         ht c h_c h_f
         (fun i => Z.spreadBound w α (η/c) m k hw hp' hy' hh ha A X (fun x=> F x.val) (fun j=>hF _) hq _ i (pow_le_one₀ hp'.le hy'))
         (fun i hj => Z.spreadBound w α (η/c) m k hw hp' hy' hh ha A X (fun x=> F x.val) (fun j=>hF _) hq _ i ((shr (A i) hj).trans
           (div_le_div_of_nonneg_right hy hc.le)))
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
    rw [tsum_fintype,Fintype.sum_sum_type]; unfold YM.MergeProof.Ribbons.Salt.scent
    refine add_le_add ?_ (le_trans (Budget.cap (hu i) univ) (by simp))
    change ∑ j:Z.Lawn×Bool, f' (Sum.inl j) ≤ v₁+v₁; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_bool]; rw [sum_add_distrib]
    exact add_le_add (Budget.cap (hv' i) univ) (Budget.cap (hv' i) univ)
end Salt
end YM.MergeProof.Ribbons.Fibers
