import YM.UVExtension.Linden.Each
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Linden
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} 
open Animals Reserves Wick Festa PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat Daisy Willow Wick Wick.Bower
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C : ℝ} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {β : ℂ} {H : Cash W x μ L Q o a T R} {V : ι → Juice G f}
variable {v₁ v₀ b₀ K' w g θ A r B' D d n' n : ℝ} {k j K : ℕ} {χ:Chi}
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)
    (M: PhysicalNext.Repeat.Lotus.Leaf R) (hl:Lines R V w (betaF G x L) M)
set_option quotPrecheck false
variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
local notation "bX"=> M.turn.badge S
local notation "Σ"=> parade (ι:=ι) (betaF G x L) g
-- keep mark functional in Real.Vac leaf. parameter θ.Input derivative.M
-- W param explicit.Crew
variable (p:Molecule S)
def pilot (X:Coat T F)(A:ℝ)(Z:ChartRatio G)(W a:ℝ)(l:ℕ)(V:ι→Juice G f)(q:Vines ι)(I:Finset (Bond f))(U:Config G c)(y:F.Slice G × Air f G):ℂ:=
   let Y:= X.wrapY y.1; let u:= steer Y A (loom Y y.2) U; let t:= vary Y U; scorched Y A I U (q none) y.2 * (if M.turn.badge S∈p then
       (M.fond t a u (t.input u):ℂ)*(∏ i∈p.erase (M.turn.badge S), amberP t R Z W a (Matter.own p) l V (q none) (q∘some) (sailplane Y A y.2 U) u (t.input u) i) else 0)
def buffer (X:Coat T F)(A:ℝ)(Z:ChartRatio G)(W a:ℝ)(l:ℕ)(V:ι→Juice G f)(q:Vines ι)(I:Finset (Bond f))(U:Config G c)(y:F.Slice G × Air f G):ℂ:=
   let Y:= X.wrapY y.1; let d:= loom Y y.2; let u:= steer Y A d U; let t:= vary Y U; scorched Y A I U (q none) y.2 * (if M.turn.badge S∈p then
       (M.fond t a u (Y.input d):ℂ)*(∏ i∈p.erase (M.turn.badge S), amberP t R Z W a (Matter.own p) l V (q none) (q∘some) (sailplane Y A y.2 U) u (Y.input d) i) else 0)
variable (hp: Healthy (temp X.x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V':E → Config G c} {τ:E}
    (ht: V' τ=X.V)(hV:Mode V' τ j u) (t:F.Slice G × Air f G) (q:Vines ι) -- S α
local notation "cA"=> (pilot M p X A Q.table (W:=W) o.a Q.halo V)
local notation "bA"=> (buffer M p X A Q.table (W:=W) o.a Q.halo V)
local notation "Λ"=> grown (ι:=ι) (betaF G x L) w
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
include H
variable (I:Finset (Bond f)) (U:Config G c)
lemma spark (d:Drums ι)(h:Λ d) : cA (hoist d) I U t= ↑((hl.leaf d h).carat I X U A Q.table p W o.a Q.halo (t.1,Wick.scaled (d none) t.2)):=by
   let u:= d none; let y:= t.2; let H':= X.wrapY t.1; have hp : 0< u:= breath (altitude (H:=H)) (show (u:ℂ)∈_ from h none); have hv:hoist d none = (u:ℂ):=rfl
   unfold Leaf.carat Leaf.chimes Leaf.floret pilot; dsimp only; push_cast; rw [hl.turn]; split_ifs; swap; · rw [mul_zero,Complex.ofReal_zero,mul_zero]
   have hb : (chunk R (blend V (d∘some)) (d none)).beta=u:= rfl; rw [Complex.ofReal_mul]; apply congr_arg₂ (·*·) (censored H' A I hp U y|>.symm) _; unfold Polar.floating; rw [hb, flown _ _ hp, embers _ _ hp]; apply congr_arg₂ (·*·)
   · unfold Leaf.paidU Leaf.fond; rw [hl.turn, hl.grain]; rfl
   rw [Complex.ofReal_prod]; exact prod_congr rfl fun j _=> Wick.originalP _ V (d∘some) Q.table_exists hp _
lemma beams : Bumps Σ (fun q=> cA q I U t):=by
  let X:= X.wrapY t.1; let p':= steer X A (loom X t.2) U; intro S' f hZ hm hf
  unfold pilot; dsimp only; apply DifferentiableOn.mul
  · let Y z:= f z none; have he:DifferentiableOn ℂ Y S':= (ContinuousLinearMap.proj (R:=ℂ) (φ:=fun _:Option ι=>ℂ) none).differentiable.comp_differentiableOn hf
    exact (((he.sub_const _).mul_const (rosined X A I U t.2:ℂ)).cexp.const_mul (Flux.scalp I X U 1 A t.2:ℂ))
  split; swap; · exact differentiableOn_const _
  exact (DifferentiableOn.fun_finsetProd (fun j _=> amp_hol _ _ _ j _ (Festa.altitude (H:=H)) _ _ _ _ _ _ _ _ f hZ hm hf)).const_mul _
include hF
include hl in
lemma surround (hv:q∈Σ)(w:F.Slice G) (y z:Air f G)(hX:X.x=x) (h:Pond.swim X' y=Pond.swim X' z): cA q Z' U (w,y)= cA q Z' U (w,z):= by
   apply equals_hoist (beams (H:=H) M p (w,y) Z' U) (beams (H:=H) M p (w,z) Z' U) (Festa.altitude (H:=H)) hF.margin hF.bound _ hv
   intro s hs; let J:= (hF.mixture s hs).some; let Y:= X.wrapY w
   rw [spark (H:=H) M hl p (w,y) Z' U s hs, spark (H:=H) M hl p (w,z) Z' U s hs]; apply congr_arg Complex.ofReal; unfold Leaf.carat Leaf.chimes
   let R':=chunk R (blend V (s ∘ some)) (s none)
   have hs':Pond.swim X' (Wick.scaled (s none) y)=Pond.swim X' (Wick.scaled (s none) z) := Festa.projection _ _ _ h _
   dsimp only; rw [Flux.slab _ _ U _ _ hs']; apply congrArg
   have hp := congr_arg (pitch Z' Y A R'.beta U) hs'; rw [pitch_alt,pitch_alt] at hp
   have hB : X'= podium S G (H.unionP p) X.B:=by rw [← chargedU (H.unionP p), show X.B=radiusB x from congr_arg _ hX]
   apply (hl.leaf s hs).census (vary Y U) p (show Intake _ _ X.x _ from hX.symm ▸ J.laws.intake) (show Room _ _ T X.x from hX.symm ▸ J.laws.data.room) Q.buys (Z:= H.unionP p) ?_ ?_
   · exact ⟨Village.refl ..,fun i hi=> (observe X').1 hp i (hB.symm ▸ hi),fun _ _=>Iff.rfl⟩ -- replace application
   · rw [show (vary Y U).B = radiusB x from congr_arg _ hX]; exact Finset.Subset.refl _

include hX hm hV ht N hr
omit [FiniteDimensional ℝ E] in
lemma bridge (hv:q∈Σ) : (fun i=> cA q I (V' i) t)=ᶠ[𝓝 τ] fun i=>bA q I (V' i) t:=by
  rcases t with ⟨c,w⟩
  let Z:= X.wrapY c; let d:=loom Z w
  have he:8*o.a*X.t≤A/2:=by unfold Coat.t; rw [hX,H.laws.data.funds.length_eq]; exact N.foot
  have hB:0< o.a*Z.t:=mul_pos o.large (H.laws.data.localP _ Z hX hr hm).sails.room.fiery
  filter_upwards [Silica.nearby Z N.bay ht hV] with t ht
  unfold pilot buffer; dsimp only; apply congr_arg; split; swap; · rfl
  let T':= vary Z (V' t); let p':= steer Z A d (V' t); let C:= sailplane Z A w (V' t)
  have hθ := conquered Z N.bay (V' t) d ht hB he; apply congr_arg₂ (·*·)
  · exact congr_arg Complex.ofReal (M.canv T' _ _ _ (plastic hθ hB))
  refine prod_congr rfl (fun i _=>?_)
  symm; apply equals_hoist (amp_hol T' V Q.table i _ (altitude (H:=H)) _ _ _ g C p' (Z.input d))
    (amp_hol T' V Q.table i _ (altitude (H:=H)) _ _ _ g C p' (T'.input p'))
    (altitude (H:=H)) hF.margin hF.bound _ hv
  intro q h; let A':= (hF.mixture q h).some; let R':=chunk R (blend V (q ∘ some)) (q none)
  have hu:0<q none := A'.laws.intake.positive
  change amberP T' R _ W _ _ _ _ (q none) ((fun i=>((q ∘ some) i:ℂ))) C _ (Z.input d) i = amberP T' R _ W _ _ _ _ (q none) (fun i=>((q ∘ some) i:ℂ)) C _ _ i
  rw [originalP _ V (q ∘ some) Q.table_exists hu, originalP _ V (q ∘ some) Q.table_exists hu]; apply congr_arg
  exact ((plastic hθ hB).reeled (show Room _ S T T'.x from hX.symm ▸ H.laws.data.room) W Q.table _ _ (show Intake _ _ T'.x R' from hX.symm ▸ A'.laws.intake) i _).symm
end YM.UVExtension.Linden
