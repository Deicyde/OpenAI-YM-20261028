import YM.Planned.PRIMARY_INTEGRAL_295.Largo
import YM.Planned.PRIMARY_INTEGRAL_295.Novas
/-!
# Deck: numerical locality in Torch no-hole and true lx forecast

Doesn't buy sizes/radii from Stamps. Used before cutting physical Y, computes
pathwise quantities, raw identities to declare later. `Shell`: current B x Orb
through ROOT.Φ Price geometry, tests on all paths incl auxiliary chart.E.
No Require.Earnings. Orbit projection elsewhere. Pose defines only unmasked
bulk0 in each input sector bank. `t` fine, T index. Alignment around gauge.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Decks
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r n d χ:ℕ} {c f:Side} {t ξ C M : ℝ}
variable {F:Labels.Frame G d} {S:StepData c f} (P:Torch G S)

-- Pointwise Cone Receipt.
structure Deck (T:SectionData F)(r k χ:ℕ)(u:ℝ):Prop where
   sees : ∀ j:P.clan.grounds, separation 0 (Density.chair S j.val)+2*Mirage.budget S.patch P.R ≤ r
   go : Trail S.ratio T r
   stars (i:P.Index) (x:P.clan.grounds): x∉P.clan.homes.W i→ χ≤separation (chair S (P.clan.bee i).val) (chair S x.val)
   doors (i:P.Index) (j:P.clan.homes.W i): ∀ a:Acres f G, a ∉ P.clan.grounds→2*Mirage.budget S.patch P.R < separation (chair S j.val.val) (chair S a)
   lands : (Fintype.card P.clan.grounds:ℝ)≤u
   length : (Fintype.card P.clan.held:ℝ)≤u
   ridge : P.ε∈Set.Ioc 0 1 ∧ 8≤u*P.ε
   pulse : ∀ x, Oval.Envelope x k P.shine.χ u
   footprint : ∀ i:Place.Spot T.stencil,∀ (z:P.clan.tree.Free), (wrap f (Place.first i).val,Place.beam i)=z.val→ z∈P.clan.held

section Market
variable {T:SectionData F} {V W:Config G c} (t ξ:ℝ)
variable (hd: Deck P T r k χ C) (hc:S.patch.Branches S.kernel G) (he:AgreeNear id 0 r V W)
include hd hc he

lemma board : P.staged V=P.staged W ∧ P.stamp V t=P.stamp W t := by
   let K:=P.core; let M:=P.clan; have hf(i j : P.clan.grounds):dark K V i.val j.val = dark K W i.val j.val ∧
       foams K V i.val= foams K W i.val:= Largo.courts _ _ _ i.val j.val hc (he.shrink (hd.sees i))
   have hs: head _ (dark K V)= head M (dark K W):= Matrix.ext (fun i j=>(hf i j).1)
   constructor
   · exact congr_arg M.homes.coin hs
   unfold Torch.stamp muster; rw [show head _ (dark _ V)=_ from hs]; exact congr_arg _ (congr_arg _ (by ext i; exact congr_arg (t⁻¹ • ·) (hf i i).2))

lemma require (i:F.Index) : P.quest V t ξ T i = P.quest W t ξ T i:=by
   obtain ⟨ha,hb⟩:=board P t hd hc he
   have hf(x:P.Starry):P.heap V t ξ T i x=P.heap W t ξ T i x:=by
     unfold Torch.heap Torch.keel; rw [hb]; apply congr_arg; apply congr_arg
     apply T.placed_local; intro i hi hj
     by_cases hp: i∈ P.clan.tree.trunks
     · exact (P.clan.tree.on_tree _ ⟨i,hp⟩).trans (P.clan.tree.on_tree _ ⟨i,hp⟩).symm
     let q:P.clan.tree.Free:=⟨i,hp⟩
     have heV(V:Config G c)(a:AxisChart G P.clan.tree):lifting P.clan.tree V a i=G.lieExp (a q)*replica S.ratio V i:= P.clan.tree.off_tree _ q
     rw [heV V,heV W]
     unfold replica; split
     · rfl
     apply congr_arg; exact he (S.ratio.parent i.1,i.2) (hd.go i.1 hi)
   unfold quest; rw [ha,funext hf]
end Market

section Charter
variable (b : E→Dir G c) (t:ℝ)
-- Worth post entries prephase. matrices arithmetic computed; not yet laws.
def pose : Gush G S E :=
    let K:=P.core
    { tree := P.clan.tree, b:=b, mean:=fun y=>P.mist (P.muster (stepped K b t y) (patchedAt K b t y)), held:=P.clan.held,
      C:=fun y=>P.rolled (stepped K b t y), ε:=P.ε, pulse:=P.shine }
def berth : Post (pose P b t) where
   hub := P.clan.grounds
   h₀ := P.clan.central
   homes := P.clan.homes
   A:= stepped P.core b t
   foam:=patchedAt P.core b t

def baron (t ξ:ℝ)(T:SectionData F) (i:F.Index) (y:E):ℂ:=
   let v:=pose P b t
   ∫ x: P.Starry,(v.globe ξ x) • ((t^(F.grades i).2)⁻¹ • T.places (Place.copy F i) 0 (v.lit t ξ y x))∂multivariateGaussian 0 (v.C y)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma chair_of_sand {y:E} (ht: ‖t • b y‖ ≤ trust S.patch S.kernel G) :
     let V:= represent (t • b y); P.staged V=(pose P b t).C y ∧ P.stamp V t=P.muster (stepped P.core b t y) (patchedAt P.core b t y) :=by
    intro V; obtain ⟨hh,hf⟩:=Night.studio P.core _ ht
    exact ⟨congr_arg P.rolled hh, congr_arg₂ P.muster hh (congr_arg (fun f:Temps G f => t⁻¹ • f) hf)⟩
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma truth {y:E} (T:SectionData F) (i:F.Index) (ξ:ℝ) (ht:‖t • b y‖≤trust S.patch S.kernel G) :
      baron P b t ξ T i y=P.quest (represent (t • b y)) t ξ T i :=by
   let V:=represent (t • b y)
   obtain ⟨hs,hv⟩:=chair_of_sand P b t ht
   unfold baron Torch.quest Torch.heap Torch.keel
   rw [hs,hv]
   rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma moment (i:P.Index) (y:E): let v:=pose P b t; let Z:= berth P b t
   (v.mean y i.1.val) i.2= P.clan.homes.morn (Z.foyer y) (Z.ash y) i:=by
    intro v Z
    unfold v pose; dsimp only
    unfold Torch.mist
    rw [Icebergs.withered,dif_pos i.1.property]; rfl

variable {T:SectionData F} (hd:Deck P T r k χ C)

include hd
omit [NormedSpace ℝ E] in
lemma dance (hh:∀ᶠ x in 𝓝 0, ‖t • b x‖ ≤ trust S.patch S.kernel G)(hc:S.patch.Branches S.kernel G):
     Mansions.Charter C t P.core (berth P b t) T.stencil k χ:=by
   let h:= pose P b t; let B:=berth P b t
   refine ⟨rfl,hd.lands,hd.stars,hd.length,hd.ridge,hd.pulse,hd.footprint,EventuallyEq.rfl,fun i=> ?_,EventuallyEq.rfl,fun _ _=>EventuallyEq.rfl,fun i j p hp=>?_⟩
   · exact Eventually.of_forall (fun a=>moment P b t i a)
   have he: (fun x=>B.A x j.val.val p)=ᶠ[𝓝 0] 0:= by
     filter_upwards [hh] with x hh
     let y:=t • b x; let a : Config G c:=represent y
     have hf := Largo.melts P.core a j.val.val p hc (hd.doors i j p hp)
     rw [show dark P.core a=P.core.Gram y from (Night.studio P.core y hh).1] at hf; exact hf
   exact ⟨he,he⟩

end Charter
end YM.Planned.PrimaryIntegral295.Decks
