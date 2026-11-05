import YM.MergeProof.North.Arbor
import YM.MergeProof.North.Liturgy
import YM.MergeProof.North.Palate
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Wiring
import YM.MultipleContact.Bunch.Frost
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Corn
import YM.MultipleContact.Bunch.Lyme
import YM.MultipleContact.Bunch.Botan
import YM.MultipleContact.Bunch.Junction
import YM.MultipleContact.Bunch.Nigella
import YM.MultipleContact.Bunch.Buoy
import YM.MultipleContact.Bunch.Gild
import YM.MultipleContact.Bunch.Farr
import YM.MultipleContact.Bunch.Billow
import YM.MultipleContact.Bunch.Blot
import YM.MultipleContact.Bunch.Pond
import YM.MultipleContact.Bunch.Shan
import YM.MultipleContact.Bunch.SkyFall
import YM.MultipleContact.Bunch.Quark
import YM.MultipleContact.Bunch.Menu
import YM.MultipleContact.Bunch.Wraith
import YM.MultipleContact.Bunch.Thumb
import YM.MultipleContact.Bunch.Arbor
import YM.MultipleContact.Bunch.Calm
import YM.MultipleContact.Bunch.Ebb
import YM.MultipleContact.Bunch.River
import YM.MultipleContact.Bunch.Liturgy
import YM.MultipleContact.Bunch.Papyrus
import YM.MultipleContact.Bunch.Wings
import YM.MultipleContact.Bunch.Palate

/- generalized from YM.MergeProof.North.Anise to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V] {B:Census V} {G:Gauge}{n:Side}{R:Rep G n}{v:V}{t a x b: ℝ}{w:V→ℝ}
variable {P:V→Motion}{E:V→Site n}{β:V→Equiv.Perm V}{μ:Name V slot→Site n}
variable {g:Name V slot→ Config G n→ℂ}{k:Name V slot→ℕ→ Config G n→ℂ} {r:Name V slot→ℂ}{J:Name V slot→ℝ} {h':Config G n→Poly (Aged V slot)} {Z y c q d z:ℝ}
variable (s l:ℕ)(η T Z:ℝ)
local notation "y!"=> Salt.scent (slot:=slot) R.p.B s (R.p.supportExponent+c) T η a b
local notation "W₁"=>Salt.tow J (R.p.supportExponent+c) η l
lemma blank_mach : Mach B 0 = 0:=by simp [Mach]
-- Project output shape. Consumer after.THaw plus
lemma grafted (A:Arsenal R)(h:Arc R g k h' v P E β μ J (R.p.supportExponent+c) (R.p.supportExponent+q) a b x r)(hr:R.activities.Valid R.p z d)(he:∀ i,i≠v → β i v=i ∧ ∀ j:slot, μ (i,j)=affine (P i).1 (E i) (μ (v,j))∧r (i,j)=scalar (P i) (r (v,j))) (hw:∀ i,0<J i)(hv:Occupancy μ s)(ht:0≤T)(hy:∀ i,J i*‖r i‖ ≤ T)(hm:0<R.p.B)(hX:0<η)(hY:η≤1)(hS:∀ i:V,coverNumber R.p.B (univ.image fun s:slot=> μ (i,s))≤ l)(hc:0≤ c)(hq:c≤ q)
    (hit:∀ U,R.eval U≠0)(hu:∀ i,w i=∏ s:slot, W₁ (i,s))(hJ: ((R.p.B + R.p.B + 1 : ℕ):ℝ)^4*(y!) ≤ c)(hξ: Real.exp (y!)-1≤ Z) :
    ∃ g:V→ Config G n→ℂ,∃ k:V→ℕ→ Config G n→ℂ,
       Served R g (fun i=>profile R.activities (k i)) (fun U=>BatchRibbon.reap (h' U)) (fun i=>μ (i,default)) w R.p.supportExponent Z ∧ (∀ i,Dominated (k i) ∧ Blade R (μ (i,default)) (g i) (profile R.activities (k i)) 0 (4*(Z/w i))) ∧ (∀ i,i≠v→ g i=stepUp (P i) (E i) (g v) ∧ profile R.activities (k i)=floatUp (P i) (E i) (profile R.activities (k v))) :=by
    obtain ⟨F',K,ψ,hΨ,-,hF,hK,hF',hK',hp,hZ,-,rfl⟩:=h.see
    let S:Salt V slot G n:= ⟨μ,r,F',K⟩; let t:=R.p.threshold; let D:=S.vessel t; have hB : S.Breeze t:=⟨hF',hK'⟩; let V₀ i U:=S.mount t i U; let V₁ i U:=S.soil t i U
    have hv' := S.rate J t (R.p.supportExponent+c) T η s _ l hw hv hy hm hX hY hS a b ht hF (hK.shrink (by linarith only [hq]) le_rfl hw) (add_nonneg R.p.exponent_pos.le hc)
    have hM:= S.turn t hB; have hE := S.wet _ hB; have hW := Salt.towP _ (R.p.supportExponent+c) _ l hw hX; obtain ⟨hb,hh⟩:= D.carries t hE W₁ w R.p.supportExponent c (y!) R.p.B hv' R.p.exponent_pos.le hW hu hJ
    have hWp i:0 < w i:=by rw [hu]; exact prod_pos fun _ _=>hW _
    have ht:=hb.shrink le_rfl hξ hWp; have hT:=hh.shrink le_rfl hξ hWp
    let y' U := Mach (Bud V) 0+ ∑ i,V₀ i U; let gy(v:V)(U):=(y' U).part ((Bud V).fire v)
    obtain ⟨k,hR,hS',hC,hJ'⟩:= plume (F:=V₀) (K:=V₁) A hr (fun i=> D.clearBurn t hE hM i) (fun i=>D.cloudy t hE hM i) ht hT hWp (fun i U=>(S.taxed t U hB i).trans (hZ ..)) hit 0
    refine ⟨gy,k,?_,fun i=>⟨(hR i).1,(by rw [show 4*(Z/w i)=2*(Z/w i)+2*(Z/w i) from (by ring)]; exact (hR i).2)⟩,fun i hi=>?_⟩
    · refine ⟨_,_,hC,Towed.sift ht,Towed.sift hT,Eq.trans ?_ hJ'⟩; funext U; unfold play; dsimp only; rw [map_smul,blank_mach,zero_add,S.yields _ U hB]
    have H: Twin S t (P i) (E i) v i (β i):=⟨(he i hi).1,fun j=>(he i hi|>.2 j).1, fun j=>(he i hi|>.2 j).2,fun p h j U=> (hp i hi|>.2 U).1 j p h, fun p h j U=>(hp i hi|>.2 U).2 j p h⟩
    have h' U:= Twin.twines H U
    constructor
    · funext U; unfold gy stepUp y'; simp_rw [blank_mach,zero_add,Poly.part_sum]; rw [Float.summer,← Equiv.sum_comp (sky (P i) (E i))]; exact Finset.sum_congr rfl fun j _=> (h' _).1 _
    funext j U; unfold floatUp stepUp; obtain ⟨j,h⟩:= (puff (P i) (E i)).surjective j; rw [← h,Equiv.symm_apply_apply, ← hS',← hS']; exact (h' _).2 _
end YM.MergeProof.BatchRibbons
