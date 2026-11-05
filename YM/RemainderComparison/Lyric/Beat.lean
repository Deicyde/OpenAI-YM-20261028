import YM.MergeProof.Lakes
import YM.RemainderComparison.Cascade.Lyre

/-!
# All-line Rally

A useful part of the comparison representation. It's important not to merge
log polymer addresses before estimating longer tails. Index levels of the thin
coefficient by arbitrary complete assignment of marks, not just by its
monomial, retain the uncut actual masks. Disconnected terms (wrt marked roots)
are obtained by product/exponentiation in the later marker calculus. Handles
the *noncoincident* mark variables real; when comparing ANY ring let the
producer identify these variables by the appropriate monomials (keeping tags
and factorials). These unmasked representatives attach exactly with
Calibration's log on all fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained
open Merge Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ} {O:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(X:Coat T F)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)
local notation "g₀" => Palette.sign M S
abbrev Drums (S:StepData c f):= Tickets (Palette.sign M S)
abbrev Keys (p : H.ThinP) := let _:=p; Drums M S
-- first-component mark assignment; before an anchor.
def toe (p:H.ThinP) (a:Drums M S) (V:Config G c):ℝ:=
  Cascade.escort (team M a) χ Q.table p.val Q.halo T W x o.K o.a V
structure Paid (N:Captain H j q d v u A b r B e n χ)(f : H.ThinP→Drums M S→ℝ):Prop where
   fare (s:H.ThinP)(p:Drums M S): 0≤ f s p
   classP (s:H.ThinP)(p:Drums M S): Cascade.Seminar (team M p) H s.val j A χ (f s p) v

variable {fC:H.ThinP→Drums M S→ℝ}{χ'} {N : Captain H j q d v u A b r B e n χ'}
omit [Fintype ι] in
lemma shows (hP : Paid M H χ' N fC) (p:H.ThinP)(i:Drums M S):
    LocalOn (H.smallAt p) (toe M H χ' p i) ∧ Measurable (toe M H χ' p i)∧ GaugeInvariant (toe M H χ' p i)∧
    (fun V=> act M H χ' V p.val i)=masked (Pressure.temp x) (H.smallAt p) (toe M H χ' p i)∧
    ∀ Y:Config G c,Healthy (Pressure.temp x) (H.smallAt p) Y→ Ore Y (toe M H χ' p i) v (fC p i) j := by
    exact Cascade.debtor (N:=N) (team M i) H (hP.classP p i) p.prop.2 (hP.fare p i)

omit [Fintype ι] in
lemma flagged_step (N: Captain H j q d v u A b r B e n χ)(p:H.ThinP)(i:Drums M S)(V:Config G c):
    act M H χ V p.val i = masked (Pressure.temp x) (H.smallAt p) (toe M H χ p i) V := by
   let m:=team M i
   have hp:(roster p.val).flags=∅:=p.prop.2
   let Z(r:Greenbelt.Reserve S):=prism T x χ o.K V (allot r)
   let F'(V:Config G c)(r:Greenbelt.Reserve S) := m.bloom (prism T x χ o.K V (allot r)) W o.a Q.table Q.halo p.val
   change likely (F' V)=masked (Pressure.temp x) (H.unionP p.val) _ V
   by_cases h: Healthy (Pressure.temp x) (H.unionP p.val) V
   · rw [masked_eq _ _ _ _ h]
     apply congr_arg likely; funext s
     have hx := (m.arc (Z s) p.val H N.oboe rfl rfl rfl hp h (y:=(0:ℝ)) (show Mode (fun _:ℝ=> V) _ j v from ⟨N.position.le,fun i=> a_oneB G _ N.position.le⟩) rfl).self_of_nhds
     rw [show F' V s= _ from m.pictured (Z s) p.val H rfl rfl hp,show (Z s).V=V from rfl,masked_eq _ _ _ _ h]; exact hx.symm
   rw [masked_ne _ _ _ _ h]; have hv(s): F' V s=0:= (m.pictured (Z s) p.val H rfl rfl hp).trans (masked_ne _ _ _ _ h)
   rw [funext hv]; unfold likely; simp

omit [Fintype ι] in
lemma lead (p:H.ThinP)(i:Drums M S)(V:Config G c)(h : toe M H χ p i V≠0) :
    Ac.Spark H.supportP p.val ∧ troupe T R Q.halo (radiusB x) p.val ∧ i.reach ⊆ p.val ∧
    ∀ a∈i.val,(M a).crest.image S.ratio.parent ⊆ H.smallAt p:=by
   have hs:i.reach⊆p.val:=by
     rw [← Palette.label]; intro j hj; by_contra hn; apply h; unfold toe Cascade.escort likely
     rw [sum_eq_zero fun i' _=> Cascade.stalk _ _ (fun he=> hn (he hj)),mul_zero]
   refine ⟨?_,?_,hs,fun a hv=> ?_⟩
   · by_contra hn; apply h; unfold toe Cascade.escort likely; rw [sum_eq_zero ?_,mul_zero]
     intro i hi
     unfold Team.picture; refine integral_eq_zero_of_ae (ae_of_all _ fun W=> if_neg (fun h=> hn h.1)) -- type head
   · by_contra hn; apply h; unfold toe Cascade.escort likely; rw [sum_eq_zero ?_,mul_zero]
     intro i hi
     unfold Team.picture; refine integral_eq_zero_of_ae (ae_of_all _ fun W=> if_neg (fun h=> hn h.2))
   refine Finset.Subset.trans ?_ (subset_biUnion_of_mem H.supportP (hs (i.reaches_of hv)))
   change _ ⊆ Matter.areas R T Q.halo (radiusB x) (sign M S a); unfold sign; rw [(M a).turn.badge_area]; exact (image_subset_image Finset.subset_union_left).trans (halo_subset _ _)

lemma boot (V:Team R) (hv:V.own=∅)(l : Molecule S) : V.picture X l W a O n = fringe X W a l R O n:=by
   have hp : V.signs S=∅:=by simp [Team.signs,hv]
   have he (X:Coat T F) (I:Finset (Tubular f G)) : V.cinema X l W a O n I=bars I X l R O W a n:=by
     unfold Team.cinema bars Team.floret; simp_rw [hp, if_pos (empty_subset _), show l\∅=l from sdiff_empty,Team.paidU,hv,prod_empty,one_mul]
   unfold Team.picture fringe; refine integral_congr_ae (ae_of_all _ fun y=>?_)
   unfold Team.grove shelter; dsimp only; split; next h=> exact congr_arg likely (funext fun i=> he ..)
   next=>rfl
omit [Fintype ι] in
lemma pivot (p:H.ThinP): toe M H χ p (Tickets.none _)=fun V=> leaflet H χ V p:=by
   ext V; exact congr_arg likely (funext fun s=> boot (prism _ _ _ _ _ (allot s)) _ (show (team M (Tickets.none g₀)).own=∅ from by simp [team,Tickets.none]) p.val)
end YM.RemainderComparison.Lyric
