import YM.UVExtension.Linden.Arc
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
variable (p:Molecule S) (hp: Healthy (temp X.x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V':E → Config G c} {τ:E}
    (ht: V' τ=X.V)(hV:Mode V' τ j u) (t:F.Slice G × Air f G) (q:Vines ι) -- S α
local notation "cA"=> (pilot M p X A Q.table (W:=W) o.a Q.halo V)
local notation "bA"=> (buffer M p X A Q.table (W:=W) o.a Q.halo V)
local notation "Λ"=> grown (ι:=ι) (betaF G x L) w
local notation "Z'"=> edgesM S (H.unionP p) (radiusB x)
local notation "X'"=> lensS Z' G
variable (Y: Mojo Q o L μ A x d v₁ j χ)
variable {m:Molecule S}
variable {U:Mixed.Costs} {z : Vines ι} {hz:z∈parade (betaF G x L) g} (B₀:Lush N hF z hz v₀ U) (h₀:0≤v₀)
local notation "Θ"=> (z none).re
-- Clutch supply can be held at real part theta, hypothesis only there.\n
include ht hX hm hS hc B₀ Y hr hV
lemma funds (z':Air f G) : Brush j M.weight (v₁ *spanW T R (radiusB x) Q.halo bX) (fun i=> (↑(M.fond (vary X (V' i)) o.a (steer X A (loom X z') (V' i)) (X.input (loom X z'))):ℂ)) τ:=by
   let U':= flight R Θ; let p:= B₀.link; let l:Leaf U':= ⟨M.turn, M.ingredient, (show UsesFinal U'.p.threshold (M.turn.support U') _ from ?_), ?_, ?_, M.weight, M.earn,M.glows,M.borel⟩; rotate_left
   · have ht:M.turn.support U'=M.turn.support R:= by cases M.turn <;> rfl
     rw [ht]; exact M.scopedR
   · intro U hx; have h:= M.grant U hx; cases hi:M.turn <;> rw [hi] at h <;> exact h
   · have h:=M.blank; cases hi:M.turn <;> rw [hi] at h <;> exact h
   let d:= Wick.scaled Θ z'; have hv:= (N.granted _ _ S T _ _ p hS rfl).2 E V' F X τ hX hc hr hm ht hV
   have he : Brush j M.weight (v₁*spanW T R (radiusB x) Q.halo bX) (fun i=> M.fond (vary X (V' i)) o.a (steer X A (worldZ X Θ d) (V' i)) (X.input (worldZ X Θ d))) τ:= Y.duck _ _ S T F X _ _ p l hX hc E V' τ d (hv.2 d|>.1)
   rw [show worldZ X Θ d= loom X z' from fanned X z' (p.laws.intake.positive)] at he; exact rises he

include hp h₀
variable (hG : troupe T R Q.halo (radiusB x) p)(hW:M.turn.badge S∈p)(I:Finset (Bond f))
include hG hW
lemma pricesB (t:F.Slice G × Air f G):
    let s:= X.catastrophe (o.ξ/2) (z none).re (blaze (p.erase (M.turn.badge S)))
    let f':=M.weight*(∏ i∈p.erase (M.turn.badge S),tabs S U (radiusB x) Q.halo B₀.peeled i)
    Brush j ((s.indicator (fun _y:Air f G=> f'*(1+v₀+2*(v₁+r))^j*(1+H.shapeW p)^j*facescale I t.2^(K*j))) t.2) 1 (fun i=> cA z I (V' i) (t.1,gStep ((z none).re) • t.2)) τ:= by
  rcases t with ⟨y,w'⟩; let P':= X.wrapY y; let q:Air f G:= gStep Θ • w'; let p'(i:E):= steer P' A (loom P' q) (V' i)
  intro S' u
  let W':= p.erase bX; let t i:=buffer M p X A Q.table W o.a Q.halo V z I (V' i) (y,q); apply Brush.shimmy (f:=t) _ (bridge N hF M hX hm hr p ht hV _ _ _ hz)
  let v:=tabs S U (radiusB x) Q.halo B₀.peeled; have hu:0 < Θ:=B₀.link.laws.intake.positive; let L:= loom P' q
  have ht' :(gStep (z none).re)≠0:=(inv_pos.mpr (Real.sqrt_pos.mpr hu)).ne'; have hk' : Wick.scaled Θ q = w':= inv_smul_smul₀ ht' _
  have hA:= B₀.conduit.active
  let l':= Matter.own p; let f(k)(i:E):=amberP (vary P' (V' i)) R Q.table W o.a l' Q.halo V (z none) (z∘some) (sailplane P' A q (V' i)) (p' i) (P'.input L) k
  by_cases h:w'∈S'
  · rw [Set.indicator_of_mem h]
    obtain ⟨hL,hQ⟩:= B₀.breathes E V' F P' hX hc hr hm τ q hV ht; specialize hL I; rw [hk'] at hL
    have hM:= funds (X:=P') N hS hF M hX hm hc hr ht hV Y B₀ q
    have he i (hi:i∈W') : Brush j (v i) (r*spanW T R (radiusB x) Q.halo i) (f i) τ := hQ _ i
      (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP (mem_of_mem_erase hi)) hp)
    have hV (i) : 0≤ spanW T R (radiusB x) Q.halo i:= by cases i; exact zero_le_one; exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hhV : v₁*spanW T R (radiusB x) Q.halo bX+(∑ i∈W',r*spanW T R (radiusB x) Q.halo i) ≤ (v₁+r)*(2*H.shapeW p) := by
       rw [← Finset.mul_sum]; have hg:= Utopia.worthy (H:=H) _ hG
       rw [← Finset.add_sum_erase _ (spanW T R (radiusB x) Q.halo) hW] at hg; rw [add_mul]; refine add_le_add (mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_right (sum_nonneg fun _ _=> hV _)) hg) Y.funded) (mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_left (hV _)) hg) (zero_le_one.trans hA))
    have H' := (hM.paints (all_thread _ _ _ _ he)).climb le_rfl hhV
    have hp' := (hL.paints H').trim
    unfold t buffer; dsimp only; simp only [if_pos hW]
    apply hp'.climb _ le_rfl; rw [one_mul]; let x:= facescale I w'; let V₁ := v₁+r; let W:=1+H.shapeW p
    have ht2:1≤V₁:= hA.trans (le_add_of_nonneg_left Y.funded); have he : 1 ≤ x^K:= one_le_pow₀ (Flux.expenses I w').1; have ht₀:1 ≤ W := le_add_of_nonneg_right (H.positive_volume p)
    have hf : 1+(v₀*x^K+V₁*(2*H.shapeW p)) ≤ (1+v₀+2*V₁)*W*x^K := by
      have hv' : x^K≤ W*x^K:= le_mul_of_one_le_left (by linarith only [he]) ht₀; have H: H.shapeW p ≤ W*x^K:= le_trans (le_add_of_nonneg_left zero_le_one) (le_mul_of_one_le_right (zero_le_one.trans ht₀) he); nlinarith only [H,hv',h₀,he,ht2,mul_le_mul_of_nonneg_left H (zero_le_one.trans ht2)]
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by exact add_nonneg zero_le_one (add_nonneg hL.pos (mul_nonneg (zero_le_one.trans ht2) (mul_nonneg (by norm_num) (H.positive_volume _))))) hf j) H'.nonneg).trans_eq
    change u*_= _; rw [mul_pow,mul_pow,pow_mul]; ring
    -- hV proof
  · rw [Set.indicator_of_notMem h]; refine Brush.zi ?_ le_rfl zero_le_one
    let Z:= B₀.link
    have hv := (N.granted c _ S T _ _ Z hS rfl).2 E V' F P' τ hX hc hr hm ht hV
    unfold S' catastrophe Poll.Crash at h; change ¬(∀ i∈_,∃ j, _≤_ ∧ _≤_) at h; push Not at h; obtain ⟨i,hi,hp⟩:= h
    let S_: Cash W P'.x μ _ Q o a T (Wick.flight R (z none).re) := hX.symm ▸ Z
    have H':worldZ P' (Wick.flight R (z none).re).beta w'=loom P' q:= by rw [← hk']; exact fanned _ _ hu
    have he:= (hv.2 w').1.sleek S_ hV hS hm hr i (fun i hi=> (hp i hi).le) l'
    filter_upwards [he] with y0 hy; unfold t buffer; dsimp only; rw [if_pos hW]
    apply mul_eq_zero.mpr; right; apply mul_eq_zero.mpr; right; change (∏ i ∈ W',f i y0)=0
    refine Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) ?_
    rw [H'] at hy; exact (congr_arg Complex.ofReal hy).trans Complex.ofReal_zero
end YM.UVExtension.Linden
#print axioms YM.UVExtension.Linden.pricesB
