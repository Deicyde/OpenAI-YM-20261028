import YM.MultipleContact.Bunch.Mutation
import YM.MultipleContact.Bunch.Himalaya

set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open YM.MergeProof YM.MergeProof.Ribbon YM.MergeProof.Ribbons YM.MergeProof.Accent
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Local Menu Extra.Histories Extra.Trajectories Motion Merge PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open Extra.Multi GridApprox.Nil Next.Rank Stock Cells PhysicalNext.Repeat.Lotus
open scoped Topology BigOperators Classical
variable {slot:Type}[Fintype slot][Inhabited slot] {G:Gauge}(C:Family G) (d:ℕ){δ:ℕ→ℝ} {r:ℕ→ℕ}
set_option quotPrecheck false
local notation "P'"=> C.path.levels.budget
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
def packet {α:Type}[Fintype α] (η:ℕ→ℝ)(i:ℕ):=η i/Fintype.card α
def division {α:Type}[Fintype α][Inhabited α] (i₀:ℕ)(η:ℕ→ℝ):Prop:= ∀ i, i₀≤ i→0<η i∧η i≤1∧ (((C.path.levels.budget i).B+(C.path.levels.budget i).B+1 :ℕ):ℝ)^4*expense (slot:=α) C.path.levels r δ (η i) i ≤1/2 ∧ Real.exp (expense (slot:=α) C.path.levels r δ (η i) i)-1≤1
lemma scent_replace (A:Levels G)(r:ℕ→ℕ) (χ η:ℕ→ℝ) (m:ℕ) (hη:0<η m)(ht:η m≤1)(hx:0≤χ m): expense (slot:=slot) A r χ (packet (α:=slot) η m) m ≤ scurry A r χ (η m) m:=by
    set x:ℝ:=(Fintype.card slot:ℝ)
    have hp : 1 ≤ x:=by change (1:ℝ) ≤ (Fintype.card slot:ℝ); exact_mod_cast (show (1:ℕ) ≤ Fintype.card slot from Fintype.card_pos_iff.mpr (by infer_instance))
    have he:r m*(Real.exp ((A.budget m).supportExponent+1/2))+1 ≥ 0:= add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) zero_le_one
    unfold packet; change expense (slot:=slot) A r χ (η m/x) m ≤ _
    unfold expense scurry BatchRibbons.Salt.scent Ribbons.Salt.scent
    push_cast; simp only [mul_one]
    set s:ℝ:=(r m:ℝ); set y:=s*Real.exp ((A.budget m).supportExponent+1/2)+1
    have hL :(1+s*x)*(η m/x) ≤ (1+s)*η m:=by field_simp; nlinarith only [hp,hη,div_mul_cancel₀ (η m) (zero_lt_one.trans_le hp).ne']
    have hX:1+s*x*(η m/x) ≤ 1+s:=by field_simp; nlinarith only [ht,show 0 ≤ s from by positivity]
    nlinarith only [mul_le_mul_of_nonneg_right hL he,mul_le_mul_of_nonneg_right hX hx]
lemma adjusted {χ η X:ℕ→ℝ}{i₀:ℕ}(hr:Wares C (δ:=δ) (r:=r) (μ:=D) i₀ d χ η X)(hx:∀ i,0≤χ i): division C (α:=slot) (δ:=χ) (r:=r) i₀ (packet (α:=slot) η):=by
    intro i hi; have hf:= hr.funs i hi; have hh:=hr.bars _ hi
    have hp : 1 ≤ (Fintype.card slot:ℝ):= by exact_mod_cast (Fintype.card_pos_iff.mpr (by infer_instance):0<Fintype.card slot)
    have he:= scent_replace (slot:=slot) C.path.levels r χ η i hf.1 hf.2 (hx i)
    exact ⟨div_pos hf.1 (zero_lt_one.trans_le hp), (div_le_self hf.1.le hp).trans hf.2,(mul_le_mul_of_nonneg_left he (by positivity)).trans hh.1,(sub_le_sub_right (Real.exp_monotone he) _).trans hh.2⟩
lemma mk_thor {χ:ℕ→ℝ}(hr:∃ s:ℕ→ℝ,∀ i,C.ref d≤ i → Duty C.path r i (δ i) (s i) (χ i) ∧ ∀ (N p:ℕ)(h:i<N),MergeProof.Menu.Volant (C.path.levels.clock.op i p) (D N p i h) (r i) ((P' (i+1)).supportExponent-4) (s i) ((P' i).supportExponent+1/2) ((P' i).supportExponent+1) 1 (χ i) ∧ ∀ (α:Type) [_h:Fintype α][_d:DecidableEq α][_i:Inhabited α], BatchRibbons.Unites (slot:=α) (C.path.levels.clock.op i p) (D N p i h) (r i) ((P' (i+1)).supportExponent-4) (s i) ((P' i).supportExponent+1/2) ((P' i).supportExponent+1) 1 (χ i)): ∃ s:ℕ→ℝ,∀(α:Type)[_h:Fintype α][_d:DecidableEq α][_i:Inhabited α],BatchRibbons.Thor (slot:=α) C.path δ r D s χ (C.ref d):=by
   obtain ⟨s,h⟩:=hr; exact ⟨s,fun α _ _ _=> ⟨fun _ _ i hI hi=>⟨((h i hI).2 _ _ hi).1,((h i hI).2 _ _ hi).2 α⟩,fun i hI=>(h i hI).1⟩⟩
lemma procure (hr:Broader C δ r D):∃ χ, (∀ i,0≤χ i) ∧ Wares C (δ:=δ) (r:=r) (μ:=D) (C.ref d) d χ δ (bling C.path.levels) ∧ ∃ s:ℕ→ℝ,∀(α:Type)[_h:Fintype α][_d:DecidableEq α][_i:Inhabited α],BatchRibbons.Thor (slot:=α) C.path δ r D s χ (C.ref d):=by
    obtain ⟨χ,hx,y⟩:=hr.mother
    exact ⟨χ,hx,(y d).1,mk_thor C d (y d).2⟩
end YM.MultipleContact.Bunching
