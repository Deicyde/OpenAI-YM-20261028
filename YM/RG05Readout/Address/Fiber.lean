import YM.RG05Readout.Address.Rail
import YM.RG05Readout.Address.Shape
/-!
# Exact physical one-slot coupons and numerical bills

Field-only costs used again with address conversions. Pin same history
before evaluation. No basis-dependent choice of output kernel or vacuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G:Gauge}(C:Family G)(N m p d:ℕ)
set_option quotPrecheck false
local notation "Z"=>C.path.levels.clock.op m p
local notation "R"=> C.path.rep N p m
local notation "M"=> C.path.rep N p (m+1)
local notation "F"=>C.labels.level d
local notation "Y"=> C.params
local notation "S"=> C.localSection d
local notation "κ"=> kappa C.path
local notation "L"=> C.path.S.block m
local notation "v"=> ((L).val:ℂ)^d
variable (o:Site (C.path.S.side (m+1) p))
variable {a c α β g r J :ℝ} {X:Extra.Histories.Heading (C.labels.level d)} (D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
-- Tribute for actual primary slot possibly unmasked exact. Bundle both budgets at t. uniform wrappers. Keep scalar when limiting.
local notation "q"=> Pricing S C.path N p m Y
variable (h:C.Makes) (hm:m<N) (ho:(C.path.levels.clock.op m p).ratio.parent o=0) (hw: Pricing (C.localSection d) C.path N p m C.params D X a c α β)
include hm h
lemma primordial (A:Extra.Histories.Heading (F)) : (Push.Local.Leading A.map.toLinearMap a)→ let z:= (F).e0; let P:= Extra.Histories.primary o z; let t:= A.leads L z; let Q:= Extra.Histories.primary (o:=(0:Site (C.side m p))) t
     Q.Format 0 Y R∧Q.remBound 0 R (κ m) 0 ∧ Ride (Z) o 0 D v (invoice P o S M) (invoice Q 0 S R) 1:=by
   intro hA z P t Q; have he: Q.Format 0 Y R:=primary_format _; have hQ: Q.remBound 0 R (κ m) 0:= primary_rem _ (Real.sqrt_pos.mpr (forcedPos ..)); have hP:P.Format o Y M:=primary_format _; have hp:P.remBound o M (κ (m+1)) 0:=primary_rem _ (Real.sqrt_pos.mpr (forcedPos ..)); refine ⟨he,hQ,⟨Useful.invoice P o (S) (M) (h.wilson.represents _ _ _ hm).good hp hP,Useful.invoice Q 0 (S) (R) (h.wilson.represents N p m hm.le).good hQ he, ?_,?_⟩⟩
   · have he : P.exponentialEntry o S M=1:=by
        funext U; have ht i:P.maskedTerm M i U=0:=congr_fun (map_zero (maskLinear _ _)) _
        change (primary (S) o (M).p.threshold (F).e0 U)+ (∑' i,P.maskedTerm M i U)=1
        rw [unit_at]; simp [ht]
     refine ⟨∅,finite_empty,1,norm_one.le,?_⟩
     change Tale (∅:Set Wing) _ _ _ (P.exponentialEntry o S M) (profile (M).activities P.forced) (profile (R).activities Q.forced) _ _ _ _
     simp_rw [he,show profile (M).activities P.forced=0 by ext; simp [profile,P,Extra.Histories.primary,cram], show profile (R).activities Q.forced=0 by ext; simp [profile,Q,Extra.Histories.primary,cram]]
     exact taped zero_le_one zero_le_one
   change Q.density 0 S R=v • (Z).push (M).beta (P.density o S M)
   have he : P.density o S M= liftVac C.path N p (m+1):= by
       funext U; unfold P; rw [primary_density]; change _*Local.primary S o (M).p.threshold (F).e0 U= _; rw [unit_at]; exact mul_one _
   rw [he,← show liftVac C.path N p m=_ from vac_transfer C.path N p m h.wilson hm]
   funext U; unfold Q; rw [primary_density]
   have ht(ζ: (F).Index): vowel F L z ζ=(v • z) ζ:=by
      by_cases h:ζ=0
      · subst ζ; simp only [vowel,(F).zero_degree, Nat.sub_zero]; rfl
      change _*z ζ= _*(z ζ); rw [show z ζ=0 from Pi.single_eq_of_ne h _]; simp
   have hy:t=v • z:=(congr_arg A.map (funext ht)).trans (Eq.trans (map_smul ..) (congr_arg (v • ·) (show A.map z=z from hA.unit)))
   change _*Local.primary S 0 (R).p.threshold t U = v*((R).eval U:ℂ); rw [hy,map_smul,unit_at]; simp only [Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one]; ring

include ho hw
lemma primary_grant (i: (F).Index) (hα:0 ≤ α)(hc:1 ≤ c)(hβ:0 ≤ β):
    let x:= Size.axis F i
    let P:= Extra.Histories.primary o x
    let u:=c*(F).coeffSize (vowel F L x)
    ∃ Q:Coefficient (F) (C.side m p), Q.Format 0 Y R∧Q.remBound 0 R (κ m) u∧ Ride (Z) o 0 D v (invoice P o S M) (invoice Q 0 S R) (1+u+β)∧ (F).coeffSize Q.x ≤ u ∧ (F).coeffSize (basisCut F (((F).grades i).1) (Q.x-X.leads L x))≤α :=by
   intro x P u; have hp:P.Format o Y M:=primary_format _; have hP:P.remBound o M (κ (m+1)) 0:=primary_rem _ (Real.sqrt_pos.mpr (forcedPos ..)); have hu: 0 ≤ u:=mul_nonneg (zero_le_one.trans hc) (Work.G08.size_nonneg ..); have hrβ:β ≤ 1+u+β:= le_add_of_nonneg_left (add_nonneg zero_le_one hu)
   have hu' : u ≤ 1+u+β:=le_trans (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_right hβ)
   by_cases hv:i=0
   · subst i; let f:= X.leads L x; let Q:=Extra.Histories.primary (0:Site (C.side m p)) f; obtain ⟨hF,hU,hA⟩:=primordial C N m p d o D h hm X hw.lower
     refine ⟨Q,hF,rem_mono hU hu, hA.cost (le_trans (le_add_of_nonneg_right hu) (le_add_of_nonneg_right hβ)),hw.norm _|>.1,?_⟩
     simp only [show Q.x=X.leads L x from rfl, sub_self,map_zero,Frame.coeffSize, Pi.zero_apply,norm_zero,Finset.sum_const_zero]; exact hα
   obtain ⟨Z',S',hZ,hY,hU⟩:=hw.buys o ho; have hs:=hU.entry i hv
   dsimp only at hs; rw [Size.core_axis (F),if_neg hv] at hs
   obtain ⟨Q,hA,hF',hW,hT⟩:=hs; refine ⟨Q,hA.format,hA.bound,⟨Useful.invoice P o (S) (M) (h.wilson.represents _ _ _ hm).good hP hp, Useful.invoice Q 0 (S) (R) (h.wilson.represents N p m hm.le).good hA.bound hA.format, ⟨S',hZ,0,(le_trans (norm_zero.le) (le_trans hu hu')),?_⟩,hA.agrees⟩,hW,hF'⟩
   change Tale S' _ _ _ _ (profile (M).activities P.forced) _ _ _ _ _
   rw [show profile (M).activities P.forced=0 from by ext; simp [profile,P,Extra.Histories.primary,cram]]; exact hT.climb le_rfl hrβ hu'

lemma regular_grant (P:Coefficient (F) (C.side (m+1) p)) (hα:0≤α) (hκ: κ (m+1) ≤ 1) (hp:P.Format o Y M)(hP:P.remBound o M (κ (m+1)) r) (hx:P.x=0):
    ∃ Q:Coefficient (F) (C.side m p), Q.Format 0 Y R∧ Q.remBound 0 R (κ m) (α*r) ∧ Ride Z o 0 D v (invoice P o S M) (invoice Q 0 S R) ((2+α)*r) ∧ (F).coeffSize Q.x ≤ α*r:=by
    obtain ⟨s,X,hZ,hY,hT⟩:=hw.buys o ho
    obtain ⟨Q,hU,hR⟩:= tracking_cost (S) C.path N p m Y o s P X D h.wilson hm hp hP hx hw.soundD hα hT hκ hY
    have hr:= rem_nonneg hP; have ht : α*r ≤ (2+α)*r:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_two) hr; have hs:0 ≤ α*r:=mul_nonneg hα hr
    refine ⟨Q,hU.format,hU.bound, ⟨Useful.invoice P o S M (h.wilson.represents _ _ _ hm).good hP hp, Useful.invoice Q 0 S R (h.wilson.represents N p m hm.le).good hU.bound hU.format,?_,hU.agrees⟩,?_⟩
    · refine ⟨X,hZ,P.x 0,?_, hR.climb le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hα) hr) ht⟩
      rw [hx,Pi.zero_apply,norm_zero]; exact hs.trans ht
    exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le _)).trans (by simpa only [sub_zero] using hU.leadP)
end YM.RG05Readout.Address
