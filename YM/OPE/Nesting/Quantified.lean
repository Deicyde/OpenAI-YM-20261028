import YM.OPE.Nesting.Kernels

/-! Uniform estimates on separated fixed trees with independent shrinking
rates, in the physical hierarchy and every viewer. Scales constrained via
whole relative displacements, as in positive clearance across sibling
clusters; immediate-position inequalities and a sufficiently small common
ratio upper bound suffice too (`Tree.of_immediate`). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Finset TopologicalSpace
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

def Buffer {I J:Type}(z:I→E4)(y:J→E4)(e:ℝ):Prop:= (∀ i j, e ≤ ‖z i-y j‖) ∧ ∀ i j:J,i≠j→ e ≤ ‖y i-y j‖
structure Accept {t:Tree} (r M η:ℝ)(s:t.Inner→ℝ)(z:t.Plot): Prop where
      levels : t.Tapered r 1 s
      relative : t.Relative M η s z
      scale : t.current s = r

namespace Limits
open _root_.YM.OPE.Nesting.Tree
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)
variable {I J L:Type}[Fintype J]{T:L→ℝ}{l:Filter L} (hT:Tendsto T l atTop) [l.NeBot]
include hT in
lemma buffer_stage {δ:ℝ}{z:L→I→E4}{y:L→J→E4}(hδ:0<δ)(hp:∀ᶠ i in l,Buffer (z i) (y i) δ):Intervals l T 0 z y ∧ Kept l T 0 y:=by
     have hv(a)(ha:0<a):∀ᶠ i in l,Real.exp ((-a)*T i)<δ:=(RateIs.exp (-a) hT).tends (neg_neg_of_pos ha) hT |>.eventually (gt_mem_nhds hδ)
     refine ⟨fun r hr=> ((hv r hr).and hp).mono fun i ⟨hi,h'⟩ u v=>hi.trans_le (h'.1 u v), fun r hr=>((hv r hr).and hp).mono fun i ⟨he,hi⟩ u v huv=> he.trans_le (hi.2 u v huv)⟩

variable {n:ℕ}{f:Fin n→Tree}{t:Tree}{M η δ ε:ℝ}(hM:0≤M)(hη:0<η)(hδ:0<δ)(hε:0<ε)
include h hM hη
local instance : Nonempty ((fork n f).Inner):=⟨Sum.inl ()⟩
private lemma parse_eventual' (t:Tree)[Nonempty t.Inner] (p:(t.Inner→ℝ) × Tree.Plot t→ Prop)
    (hp:∀ (r:ℝ→t.Inner→ℝ)(z:Envelope ℝ t)(ψ:Filter ℝ)(_:ψ.NeBot), ∀ (T:ℝ→ℝ)(a:t.Inner→ℝ), (∑ v,a v)=1 → Tendsto T ψ atTop → (∀ v,RateIs ψ T (fun i=>r i v) (-a v)) → t.Regular ψ T 0 a z → t.ordered 0 a → ∀ᶠ i in ψ,p (r i,z i)) : ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:t.Inner→ℝ)(z:Tree.Plot t), Accept r M η s z → p (s,z):=by
      have hv:∀ᶠ r:ℝ in 𝓝[>]0,∀ v:_ × Tree.Plot t,Accept r M η v.1 v.2 → p v := by
           refine refine_geometry (V:=(t.Inner→ℝ) × Tree.Plot t) (Q:=fun _ v=>p v) fun f ψ hN h' he=>?_ 
           let s:= Prod.fst ∘ f; let z:=Prod.snd ∘ f
           obtain ⟨χ,hb,hh,T,a,ha,hT,hs,hg,ht⟩:=t.find_layers (s:=s) (z:=z) (M:=M) (η:=η) (tendsto_id.mono_left h': Tendsto id ψ _) (he.mono fun l he=>⟨he.levels,he.relative⟩) hM hη
           exact ⟨χ,hb,hh, hp s z χ hb T a ha hT hs hg ht⟩
      exact hv.mono fun i hi s z hp=> hi (s,z) hp

include R U hε
lemma coe_power (v:(fork n f).Leaf→S.Tag)(m:ℕ)(c:R.channels m)(D:(fork n f).Inner→ℕ):
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:Tree.Plot (fork n f)), Accept r M η s z →
    orbitMargin R.port m (Tree.profile z) (anchor z) ∧ z∈Kernel.aperture U R (fork n f) m D ∧ ‖Kernel.output U R z v c‖ ≤ toll (wages v) ε m s ∧ ‖Kernel.output U R z v c - Kernel.chord U R z v c D‖ ≤ bothToll (wages v) ε m D s:=by
      refine parse_eventual'  h hM hη (fork n f) (fun q=> orbitMargin R.port m (Tree.profile q.2) (anchor q.2) ∧ q.2∈Kernel.aperture U R (fork n f) m D ∧ ‖Kernel.output U R q.2 v c‖ ≤ toll (wages v) ε m q.1 ∧ ‖Kernel.output U R q.2 v c - Kernel.chord U R q.2 v c D‖ ≤ bothToll (wages v) ε m D q.1) fun s z ψ hB T a h₀ ht hs hg ha=> ?_
      have hf:=Tree.profile ∘ z; obtain ⟨b,he,hb⟩:= (Fusion.tariff U R ht h _ 0 a z v hg).1.clients
      obtain ⟨-,hp,-⟩ := (hb b le_rfl).1 ()
      have h₂:= Measures.shrink_comp hg.vanish (leafSeat _); have he':=eventually_dock R.port h₂ hp.inject m
      filter_upwards [admit_nesting U R h ht v hg hs ha h₀ hε c D,admit_output U R h ht v hg hs ha h₀ hε c, Kernel.aperture_eventually (D:=D) U R ht hg m,he'] with i h₁ hh he ht
      rw [Kernel.resonantFork] at h₁; exact ⟨ht,he,hh,h₁⟩

include hδ
lemma tested_power (v:(fork n f).Leaf→S.Tag)(w:J→S.Tag)(m:ℕ):
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:Tree.Plot (fork n f)) (y:J→E4),Accept r M η s z → Buffer z y δ→
    Kernel.cardPanel z y ∈ Orbits.guardZone U R m ∧ ‖Kernel.normData U R z v m y w‖ ≤ toll (wages v) ε (m+1:ℝ) s ∧ ∀ q:Viewers U, ‖Kernel.pipe U R z v q m y w‖ ≤ toll (wages v) ε (m+1:ℝ) s:=by
    let t:=fork n f; let V:= (t.Inner→ℝ) × (t.Plot) × (J→E4); let P r (q:V):= Accept r M η q.1 q.2.1 ∧ Buffer q.2.1 q.2.2 δ
    let bill(s:t.Inner→ℝ):=toll (wages v) ε (m+1:ℝ) s
    let Q (x:V):= Kernel.cardPanel x.2.1 x.2.2∈guardZone U R m ∧ ‖Kernel.normData U R x.2.1 v m x.2.2 w‖ ≤ bill x.1 ∧ ∀ q:Viewers U, ‖Kernel.pipe U R x.2.1 v q m x.2.2 w‖ ≤ bill x.1
    refine (refine_geometry (φ:=𝓝[>]0) (P:=P) (Q:=fun _ v=>Q v) ?_).mono fun r hr s z w hp hq=>hr (s,z,w) ⟨hp,hq⟩ -- binder s z w weird s=scale z pos y ext named w shadows
    intro x ψ hB hb hx; let z:=Prod.fst ∘ (Prod.snd ∘ x); let y:= Prod.snd ∘ (Prod.snd ∘ x); let s:= Prod.fst ∘ x
    have hr:Tendsto id ψ (𝓝[>](0:ℝ)):=tendsto_id.mono_left hb
    obtain ⟨χ,h_c,hχ,T,a,h₀,ht,hs,hg,ha⟩ := t.find_layers (s:=s) (z:=z) hr (hx.mono fun i ⟨h,_⟩=> And.intro h.levels h.relative) hM hη
    have hh:∀ᶠ i in χ, Buffer (z i) (y i) δ:=(hx.mono fun i h=> h.2).filter_mono hχ
    obtain ⟨hi,h_y⟩:=buffer_stage ht hδ hh
    have hK:=all_kernel U R h ht v hg hs ha h₀ hε w hi h_y m
    have hx:=space_kernel U R h ht v hg hi h_y
    let k:=Tree.profile ∘ z
    have hD(p:Fin (m+1)): ∀ᶠ i in χ, orbitMargin R.port p.val (k i) (anchor (z i)):= eventually_dock _ (Measures.shrink_comp hg.vanish t.leafSeat) (hx.mono (fun i h=> (beside_distinct.mp h.1).1)) _
    refine ⟨χ,h_c,hχ,?_⟩
    exact ((hx.and hK).and (eventually_all.mpr hD)).mono fun i ⟨⟨hx,hK⟩,hD⟩=>⟨⟨fun j hj=>hD ⟨_,Nat.lt_succ_of_le hj⟩,hx⟩,hK.2,hK.1⟩

end Limits
end YM.OPE.Nesting
