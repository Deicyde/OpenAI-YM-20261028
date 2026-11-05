import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Mercury
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Sterad

/-! # Mercury preledger. Stable at evaluated planar. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n l k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Tubular f G)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {Ñ : ChartRatio G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E}
variable {z : Air f G} {H : Cash W s μ L Q o C T R} (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K)

-- numerical local stencil equality, even when cactus outside Health.
lemma spices (p : Molecule S) (H : Cash W s μ L Q o C T R) (X : Coat T F) (hX:X.x=s) (U Z : Config G c)
    (hv : Agrees (H.unionP p) U Z) (hf : Healthy (Pressure.temp s) (H.unionP p) X.V) (he : (roster p).flags=∅)
    (Y:S.Choices) :
    let I:=podium S G (H.unionP p) (radiusB s)
    bars I (vary ((planted X p).taggedL Y) U) p R Q.table W o.a Q.halo=
      bars I ((preps (vary X Z) (roster p)).taggedL Y) p R Q.table W o.a Q.halo := by
  intro I
  let T:= H.laws.data; let A:= vary ((planted X p).taggedL Y) U; let A':=(preps (vary X Z) (roster p)).taggedL Y
  have hh : I=podium S G (H.unionP p) A.B := by unfold I; change _=podium S G _ (radiusB X.x); rw [hX]
  have hk : Village A A' (H.unionP p) := by
    refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,hv⟩
    intro i hi; have he':i∉ RG.flags (Pressure.temp X.x) X.V:= by rw [hX]; exact Finset.disjoint_left.mp hf hi
    unfold A A' vary taggedL planted preps place; simp [he,he']
  rw [hh]; exact Shield.synchron A (show Intake P _ A.x R from hX.symm ▸ H.laws.intake) p
    (by change ground R _ Q.halo (radiusB X.x) p ⊆ H.unionP p; rw [hX]; exact Finset.Subset.refl _)
    (show Room P S _ A.x from hX.symm ▸ T.room) hk Q.buys _ _ _

structure Oboe (H : Cash W s μ L Q o C T R) (j : ℕ) (u K : ℝ) (l : ℕ) (A b : ℝ)
    (Ξ : Utopia H j u d r C' χ) : Prop where
  conduit : Canary G A b
  mode : 8*o.a*Pressure.fiery G s L ≤ A/2
  delta : FlareW H Ξ A K l
  flow : ∀ (F : Forest S.ratio) (X:Coat T F), X.x=s→ X.χ=χ→ X.width=o.K → X.manifest → ∀ (E:Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E→Config G c) (x:E),
      U x=X.V→ Mode U x j u → Glass P X U x j W

namespace Oboe
variable {Ξ : Utopia H j v d r C' χ}
include hX hK
lemma carapace (p : Molecule S) (h : Oboe H j v B l A b Ξ) (he : (roster p).flags=∅)
    (ht : Ac.Spark H.supportP p) (hR : troupe T R Q.halo (radiusB s) p) (hp : X.χ=χ)
    (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) (m : Mode V x j v) (hv : V x=X.V) :
    Brush j (B*Ξ.meant p l) 1 (fun i=> seating (H.unionP p) (radiusB s) (vary X (V i)) W o.a Q.halo p R Q.table) x := by
  let Z i:= (preps (vary X (V i)) (roster p)); let Q' k:= (planted X p).taggedL k
  let a:= podium S G (H.unionP p) (radiusB s); let f k (i:E):= bars a ((Z i).taggedL k) p R Q.table W o.a Q.halo
  have hf k:Brush j (B*Ξ.meant p l) 1 (f k) x := by
    have hzeta:(Q' k).manifest:=planted_valid X p
    have hh:=h.flow F (Q' k) hX hp hK hzeta E V x hv m
    refine (Flux.coterie (X:=Q' k) H hX hzeta hK hh h.conduit h.mode Ξ h.delta hp p hR ht (?_: Healthy (Pressure.temp (Q' k).x) _ _) m).shimmy
      (Eventually.of_forall (fun i=> (spices p H X hX (V i) (V i) (fun _ _ _=>rfl) hy he k).symm))
    change Healthy (Pressure.temp X.x) _ X.V; rw [hX]; exact hy
  let v:ℝ:=Fintype.card S.Choices; have hp :0<v:=by unfold v; positivity
  apply ((Brush.spree _ f _ zero_le_one (fun i (_:i∈univ)=> hf i)).smul v⁻¹).climb _ le_rfl
  rw [sum_const,nsmul_eq_mul,card_univ, Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel_left₀ hp.ne' _]
lemma castles (p : Molecule S) (h : Oboe H j v B l A b Ξ) (hB : 0≤B) (he : (roster p).flags=∅)
    (hp : X.χ=χ) (hy : Healthy (Pressure.temp s) (H.unionP p) X.V) (m : Mode V x j v) (hv : V x=X.V) :
    Brush j (B*Ξ.meant p l) 1 (fun i=> shelter (vary X (V i)) W o.a p R Q.table Q.halo) x := by
  unfold shelter; simp_rw [show ∀ y, (vary X y).B= radiusB s from fun y=> congr_arg _ hX]
  split_ifs with hx
  · exact Oboe.carapace hX hK p h he hx.1 hx.2 hp hy m hv
  exact Brush.zi EventuallyEq.rfl (mul_nonneg hB (Ξ.meant_nonneg l p)) zero_le_one
omit hX hK in
lemma ell (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0<W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W)
      (A f : ℝ), Canary G A f → ∀ (V : ℝ→ℝ), Rate G L (-(1/2)) V → (∀ᶠ x in atTop,0≤V x) →
    ∃ (C : ℝ) (q r p : ℝ→ℝ) (l:ℕ), Rate G L 0 p ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f') (C':ℝ) (H:Cash W x μ L Q o C' T R), ∃ Ξ : Utopia H i (V x) (q x) (r x) C χ, Oboe H i (V x) (|p x|) l A f Ξ := by
  obtain ⟨n,hN⟩:= Flux.launch P Q
  refine ⟨n,fun L hL D hD i χ W hW μ hm o A f hA V hV hv=>?_⟩
  obtain ⟨C,q,r,p,l,-,hp,hX⟩:= hN L hL D hD i χ W hW μ hm o A f hA V hV hv
  have hG:= Glass.portal P D L hD i χ hV hv o.K o.γ W o.indexPay o.f
  refine ⟨C,q,r,p,l,hp,?_⟩
  filter_upwards [hX,hG] with x hx hy c f' S T hS hT R C' H
  obtain ⟨hz,Ξ,hq⟩:= hx c f' S T hS hT R _ H
  have hg:= H.laws.data
  exact ⟨Ξ,hA,hz,hq,fun F X hX hF hv hm=> hy c f' S T hS hg.funds hg.access F X hv hF hX (hg.localP F X hX hv hm)⟩
end Oboe
end YM.ConnectedActivityE6.Blaze
