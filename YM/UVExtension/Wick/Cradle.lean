import YM.UVExtension.Wick.Oak

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' t n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
variable (z : Vines ι) (hv:z∈parade (ι:=ι) (betaF G x L) g)
set_option quotPrecheck false
local notation "β" => z none
local notation "θ" => (z none).re
local notation "Ψ" => z ∘ some
variable (hq : ‖z none‖/ (z none).re≤2)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V': E → Config G c} {τ:E}
    (ht:V' τ=X.V) (hM:Mode V' τ j u)
local notation "S₁"=> steer X A
local notation "P₁"=> warmth X
-- shift complex phase absorbs into income after exact forestry. Requires Healthy for packet with V unchanged; not required for forced sector tested values. 
variable {Z:Cash W x μ L Q o a T (flight R (z none).re)} (Ξ:Utopia Z j u d r C χ)
include N hS hF hX hm hc hr hv hq ht hM
lemma starbud (hn:0≤n) (p : Stores S) (hz:Packets.connected S Q.halo X.B p) (hp:Healthy (temp X.x) (p.dome (Q.halo*X.B)) X.V) (k : Finset ℕ) (z':Air f G)
    (a' : ℝ)(ha : Brush j a' 1 Complex.exp 0) (p':ℝ)(h' : ‖warmth X θ β p (roots X (S₁ (loom X z') X.V) (X.input (loom X z')) p)‖ ≤ Wick.chimney p p' G L x) :
    let W' i:= vary X (V' i); Brush j ((Wick.chimney p p' G L x * Ξ.tag (.inl p)) * ((1+r)+(1+j.factorial*a')*(1+48*n*p.shares))^j) 1 (fun i=>
      amberP (W' i) R Q.table W o.a k Q.halo V β Ψ (sailplane X A z' (V' i)) (S₁ (loom X z') (V' i)) (X.input (loom X z')) (.inl p)) τ := by -- W shadow
  intro T'; let d':=θ; let f' i:= S₁ (loom X z') (V' i)
  obtain ⟨p₂,hh,hb,hp',⟨H₂⟩⟩:= drift hF z hv; have hz' := (marching z).1 hv; have hu:0<d':= breath (Festa.altitude (H:=H)) hz'.1
  let U:= X.input (loom X z'); let Y:=Ξ.tag (.inl p)
  let v t := plumeLog (T' t) o.a (flight R d') Q.table (f' t) U p
  let w' t:= plumeLog (T' t) o.a (flight R p₂) Q.table (f' t) U p
  let b t:= roots (T' t) (f' t) U p
  have hv' : worldZ X d' (scaled d' z')=loom X z':= fanned _ _ hu
  let g i:= Polar.stock (T' i) o.a (flight R d') W Q.table (f' i) U k p
  have hi := (N.granted _ _ _ _ _ _ Z hS rfl).2 E V' F X τ hX hc hr hm ht hM|>.2 (scaled d' z')
  have ht0 : Brush j Y r g τ := by
    have hx' : Healthy (temp X.x) (Z.supportP (.inl p)) X.V := by rw [show X.B=radiusB x from congr_arg radiusB hX] at hp; exact hp -- danger dependent
    have hh := Ξ.stream E F X V' _ _ τ _ hX hr hc hm hM hi.1 k (.inl p) hx'
    have heZ : ∀ x', ember (vary X (V' x')) o.a (flight R θ) W Q.table (steer X A (worldZ X (flight R θ).beta (scaled d' z')) (V' x')) (X.input (worldZ X (flight R θ).beta (scaled d' z'))) (course X A (flight R θ).beta (scaled d' z') (V' x')) k Q.halo (.inl p)=g x':= fun y=> by
      change (if Packets.connected S Q.halo X.B p then Polar.stock (vary X (V' y)) o.a (flight R θ) W Q.table (steer X A (worldZ X d' (scaled d' z')) (V' y)) (X.input (worldZ X d' (scaled d' z'))) k p else 0)=_; rw [hv',if_pos hz]
    have hL:R.beta=R.beta:=rfl
    change Brush j _ (r* (1:ℝ)) _ τ at hh
    rw [mul_one] at hh; simp_rw [heZ] at hh
    unfold Y Utopia.tag; rw [← show X.B=_ from congr_arg radiusB hX]; exact hh
  have heq (i) : amberP (T' i) R Q.table W o.a k Q.halo V β Ψ (sailplane X A z' (V' i)) (f' i) U (.inl p)= (warmth (T' i) θ β p (b i) * (g i:ℂ)):= by
    unfold amberP; dsimp only [Sum.elim]; rw [if_pos (show connected S Q.halo (T' i).B p from hz),warmth_same (T' i) (v:=θ) β p _ hu,
      mul_comm (warmth (T' i) 1 _ p _),mul_assoc,← plume_warm _ _ _ p zero_lt_one hu Q.table_exists]
  change Brush j _ 1 (fun i=> amberP _ _ _ _ _ _ _ _ _ _ _ (f' i) U _) _
  simp_rw [heq]
  by_cases hy : (fun i=> X.enforce o.a (f' i) (X.plaza (p.dome (304*X.B))))=ᶠ[𝓝 τ] fun _=>0
  · have hg:g=ᶠ[𝓝 τ] fun _=>0:= by
      filter_upwards [hy] with i hi
      unfold g Polar.stock; split
      next =>
        dsimp only; change _ * X.enforce o.a (f' i) (X.plaza (p.dome (304*X.B)))=0
        rw [hi,mul_zero]
      exact rfl
    apply Brush.zi (hg.mono (fun i hi=> by change _ * ((g i:ℝ):ℂ) = 0; rw [hi, Complex.ofReal_zero,mul_zero])) ?_ zero_le_one
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Ξ.tagged _)) (by have h:=Ξ.active; have hx:= ha.nonneg; positivity)
  have hv : Brush j (n*p.shares) 1 (fun i=> v i-v τ) τ:= by
    have hhZ:worldZ X (flight R (z none).re).beta (scaled d' z')=loom X z':= hv'; have hi := hi.2.2
    simp_rw [hhZ] at hi; exact hi p hy U
  have ht'' : Brush j (n*p.shares) 1 (fun i=> w' i-w' τ) τ := by
    have hhZ:worldZ X (flight R p₂).beta (scaled p₂ z')=loom X z':= fanned _ _ hh
    have he := (((N.granted _ _ _ _ _ _ H₂ hS rfl).2 E V' F X τ hX hc hr hm ht hM).2 (scaled p₂ z')).2.2
    simp_rw [hhZ] at he; exact he p hy U
  let f0 i:= (β - (d':ℂ))*(b i:ℂ)+(amber X p:ℂ)*(Complex.log β - (Real.log d':ℂ))
  obtain ⟨hn',hk⟩:= two_pay (r:=β) rfl hq hu hp'
  have hEq i : f0 i-f0 τ = ((β-(d':ℂ))/((p₂-d':ℝ):ℂ)) * (((w' i-w' τ) - (v i-v τ):ℝ):ℂ) := by
    have hζ i:w' i=v i+(p₂-d')*b i+amber X p*(Real.log p₂-Real.log d'):= steer_plume (T' i) _ _ _ hu hh Q.table_exists
    rw [hζ i,hζ τ]
    unfold f0; have ht:((p₂-d':ℝ):ℂ)≠0:= Complex.ofReal_ne_zero.mpr hn'
    push_cast at ht ⊢; field_simp; ring
  have hh' : Brush j (48*n*p.shares) 1 (fun i=> f0 i - f0 τ) τ:= by
    simp_rw [hEq]
    apply (scales (rises (ht''.separating hv)) _).climb _ le_rfl; exact le_trans (mul_le_mul_of_nonneg_right hk (ht''.separating hv|>.nonneg)) (le_of_eq (by ring))
  have ht' := shimmers hh' ha; rw [mul_one] at ht'
  have hp : ‖Complex.exp (f0 τ)‖=‖warmth X d' β p (roots X (S₁ (loom X z') X.V) (X.input (loom X z')) p)‖ := by unfold f0 b T' f'; rw [ht]; rfl
  have hg : (fun i=> warmth (T' i) θ β p (b i) * (g i:ℂ)) = fun i=> Complex.exp (f0 i)*(g i:ℂ):=rfl
  rw [hg]; apply ((ht'.climb (hp.trans_le h') le_rfl).paints (rises ht0)).trim.climb _ le_rfl
  apply le_of_eq; ring
end Bower
end YM.UVExtension.Wick
