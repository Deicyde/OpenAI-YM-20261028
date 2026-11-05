import YM.RG08.April.Length
import YM.RG08.Oasis.Slick
import YM.RG08.Yamen.Rune
/-! # Before-level entrance gate for marks, width-specific.
 Supplies strengthening uses neighbor-positive widths delivered by leases. All frames are
 construction chosen (G,d data BEFORE length). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.June
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Rate.Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow April
open scoped Classical Matrix BigOperators PowerSeries Topology ENNReal
variable {X Z:Type}{G:Gauge}{D d p l e n k r:ℕ}(F:Labels.Frame G d)
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover

lemma classics (G:Gauge)(hG:G.Simple)(C:Family G)(h:UVExtension.Oasis.Floral (hG:=hG) C): C.params=(Next.Foundations.hol G)∧ C.labels=frames G∧ HEq C.localSection (Next.Foundations.localSection G):=by
 obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,rfl,_⟩:=h; exact ⟨rfl,rfl,HEq.rfl⟩
-- one FORE pair & stage pre. deliver cost bound $A0^2$ beyond length, forms pure gates no width post.
lemma rungs (D k j t:ℕ)(A:Hol G)(K:KernelChoices)(σ τ η U:ℝ)(hp:0<σ)(he:0<η)(hk:η≤1)(ht:2*η≤τ)(hU:0≤U)(hd:d+1≤D)(hJ:4≤j)(hT:4≤t)(hd':d≤j):∃ (μ:ℝ)(hf:Font d D k j t σ τ η μ U)(u:ℕ),∀ L:Side,u≤L.val →
 (2*η)/(L.val:ℝ) ≤ μ∧ η*Carrier.unitStep L ≤ σ/2∧ ∀ (e l n:ℕ)(he:e≤k)(hl:l≤d)(hn:n≤l+e),(April.cap F D k j t l e n A K σ η τ μ U hf hl he hn)^2 ≤ (L.val:ℝ):=by
 let P:ℝ:=((k+1)*(d+k+1):ℕ)
 have hP:0<P:=by unfold P;positivity
 let μ:=min 1 (σ/(2*P));have hm:0<μ:=lt_min zero_lt_one (by positivity)
 have hF:Font d D k j t σ τ η μ U:=by
    refine ⟨fun l e n hl hv hn=>⟨hp,(by linarith only [ht,he]),he,hU,hn,hJ,hT,hd',hd,hm.le,min_le_left .., ?_,ht,hk⟩⟩
    have ha:P*μ≤σ/2:=by
      apply le_trans (mul_le_mul_of_nonneg_left (min_le_right ..) hP.le);apply le_of_eq; field_simp
    apply le_trans (mul_le_mul_of_nonneg_right _ hm.le) ha
    unfold P;exact_mod_cast (Nat.mul_le_mul (Nat.add_le_add_right hv 1) (Nat.le_succ_of_le (Nat.add_le_add hl hv)))
 let J:= {o: Fin (k+1)×Fin (d+1)×Fin (d+k+1)//o.2.2.val≤o.1.val+o.2.1.val}
 let w(i:J):ℝ:=(April.cap F D k j t i.val.2.1.val i.val.1.val i.val.2.2.val A K σ η τ μ U hF (by have :=i.val.2.1.isLt;omega) (by have :=i.val.1.isLt;omega) (by have :=i.property;omega))^2
 let Q:=∑ i,w i;have hw(i):0 ≤ w i:=sq_nonneg _; have hQ:0 ≤ Q:=sum_nonneg fun i _=>hw _
 obtain ⟨u,hu⟩:= exists_nat_gt (Q+2*η/μ+2*η/σ)
 refine ⟨μ,hF,u,fun L hL=>?_⟩
 have hv:0<(L.val:ℝ):=by positivity
 have h0:=hu.trans_le (Nat.cast_le (α:=ℝ)|>.mpr hL)
 have hm':0 ≤ 2*η/μ:=by positivity
 have he':0 ≤ 2*η/σ:=by positivity
 have h1:(2*η)/μ≤ (L.val:ℝ):=by linarith only [h0,hQ,he']
 have h2:(2*η)/σ≤ (L.val:ℝ):=by linarith only [h0,hQ,hm']
 rw [div_le_iff₀ hv,mul_comm]; constructor
 · simpa [mul_comm] using (div_le_iff₀ hm).mp h1
 constructor
 · change η*(L.val:ℝ)⁻¹≤_;rw [←div_eq_mul_inv,div_le_iff₀ hv]; nlinarith only [(div_le_iff₀ hp).mp h2]
 intro e l n he hl hn
 let a:J:=⟨(⟨e,by omega⟩,⟨l,by omega⟩,⟨n,by omega⟩),by dsimp only;omega⟩
 exact (single_le_sum (s:=univ) (f:=w) (fun i _=>hw i) (mem_univ a)).trans (show Q ≤ _ by linarith only [h0,hm',he'])
end YM.RG08.June
