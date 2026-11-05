import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Dent
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Pairing
/-!
# Relative local column recoil :: price on scalar allowance axis

Pay the mismatch of Rows' and Aff's D; no derivative bounds on determinants
asserted here. All statements about the actual arguments, shrinking in x.
Uses bump kick locality and gauge covariance, local flat pose, actual row
plus perturb estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     PhysicalGuard7f546.Curved AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps 
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x β B C : ℝ} {X : Config G f}

lemma bump_at (P : Teller G) (D : Patch) (hD : D.Branches P.bind G) (r : ℕ) :
  ∀ᶠ x in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=D → P.Funds S T →
   ∀ (A : Stores S) (V : Config G c), Aff.cert S x A V → ∀ (p : Slots S) (k : S.Choices) (w : Directions G f),
     Aff.base S p ∉ A.dome (30*radiusB x) → (∀ i : Bond f,separation (Aff.base S p) (Aff.home S i) ≤ radiusB x → ‖w i‖ ≤ Rates.allowance G D x 1 r) →
       ‖Rows.bump T x V k w p-Aff.derivative T (till x) p V w‖ ≤ Rates.allowance G D x 2 (12+r) := by
  obtain ⟨C,δ,hC,hδ,h⟩:= pulse_cost G D P.bind P.top.clip P.top.paths hD P.top.paths_pos.le
  obtain ⟨E,hE,H⟩:= Aff.perturb P D hD
  filter_upwards [Aff.prepare D, Work.E01.radiusB_tendsto.eventually_ge_atTop 200,small_span D,remote_pose G D, Aff.chord_price G D 7,
    Rates.tariff_paid G D 3, Rates.widen G D 1 (show 6≤8 by decide),
    (Rates.vanishes G D 8).eventually (ge_mem_nhds hδ), Rates.grow G D (2*C+E) (by omega : 9+r<12+r) 2]
    with x he hB hx hV hv hb ht hp hy c f S T hS hP A V hA p k w hi hw
  let i:= Aff.base S p; let z:= YM.Next.Rank.Spindle.fingers V i; let g:=Lattice.gauge z V; let m:=radiusB x
  obtain ⟨b,hv',h1,h2,h3⟩:= hV S A V hS hA.1 hA.2 i hi
  let Y:= Rates.allowance G D x 1 r; let L:= Rates.allowance G D x 1 8
  have hY:0≤Y:=Rates.allowance_nn ..; have hL:0≤ L:= Rates.allowance_nn ..
  have hh : clearanceFare x ≤ L:= by
    apply le_trans ?_ (hb.trans ht); unfold clearanceFare Aff.tariff
    push_cast; gcongr; exact temp_nonneg _; have ht':2≤(radiusB x:ℝ):= by exact_mod_cast (hB.trans' (by decide))
    linarith only [ht']
  let t:=Aff.rotateG w (z ∘ S.ratio.parent); let t₀:= peon (S:=S) t i m
  have hz j (he : separation i (Aff.home S j) ≤ m) : t j=t₀ j:= (if_pos he).symm
  have ht': ‖t₀‖ ≤ Y:= by
    refine (pi_norm_le_iff_of_nonneg hY).mpr fun p=> ?_
    unfold t₀ t peon Aff.rotateG; split
    next he => rw [G.norm_adjoint]; exact hw p he
    next => rw [norm_zero]; exact hY
  let B:= Aff.stencilD S.patch (till x)
  have hB : 4*B+10≤m:= by unfold m B; rw [hS]; exact he.1.trans (by omega)
  have hl j (hk : separation i j.1 ≤ 4*B+1) : G.chord (g j) ≤ L:= by unfold g z; rw [hv' _ (show separation i j.1 ≤ 6*radiusB x by unfold m at hB; omega)]; exact hv c b h1 _
  let u := Rows.bump T x g k t₀ p; let y := Rows.bump T x (1:Config G c) k t₀ p
  obtain ⟨Λ,M,Hup,Hdn⟩:=hP.feeds
  have hU : ‖u-y‖≤ C*(1+(till x:ℝ))*L*Y:=
    (h L hL hp S hS hP.knobs T _ _ hP.high Hup x i m g (fun p hu=> (h3 p (hu.trans (show _ ≤ _ by unfold m; omega))).trans hh) t₀ (fun _ he=>if_neg he) k p (by obtain ⟨s,j|j⟩:=p <;> rw [show Remote.aim _ _=i from rfl,separation_self,zero_add]; all_goals exact hx.trans (by omega))).trans (mul_le_mul_of_nonneg_left ht' (by positivity))
  let K:= Aff.derivative T (till x) p g t₀
  have hf : ‖y-K‖ ≤ E*((4*B:ℕ)+1:ℝ)*L*Y:= by
    unfold y; rw [concord P hP, norm_sub_rev]; exact H c f S T hS hP (till x) p t₀ Y L hY hL (fun i _=>(norm_le_pi_norm t₀ i).trans ht') g hl
  let B₀ := (m:ℝ)
  have H : B₀*L*Y = Rates.allowance G D x 2 (9+r):= by unfold B₀ L Y Rates.allowance m Rates.pieces; ring
  have Hk : 0≤C*B₀*L*Y:= by positivity
  have Ht: ‖u-K‖ ≤ Rates.allowance G D x 2 (12+r):= by
    apply (norm_sub_le_norm_sub_add_norm_sub u y K).trans; apply le_trans (add_le_add hU hf)
    rw [← H] at hy
    let r':=radiusB x
    have hh₁:1+(till x:ℝ) ≤ (r':ℝ):= by exact_mod_cast (show 1+till x≤_ by unfold Next.SectorChange.span at hx; unfold r'; omega)
    have hh₂:(((4*B:ℕ):ℝ)+1) ≤ (r':ℝ):=by exact_mod_cast (show 4*B+1≤radiusB x by unfold m at hB; omega)
    linarith only [hy,Hk,mul_le_mul_of_nonneg_right hh₁ (show 0≤C*L*Y by positivity),mul_le_mul_of_nonneg_right hh₂ (show 0≤E*L*Y by positivity)]
  have hr:= funds_branch hP
  have hi' : u=Rows.bump T x g k t p:= by
    unfold u t₀
    obtain ⟨s,j|j⟩:=p
    · apply bump_dep T x _ _ _ (.inl j) _ _ hr; exact fun e hv=> (hz e (((contains ..).mp hv).trans (hS.symm ▸ hx.trans (by omega)))).symm
    apply bump_dep T x _ _ _ (.inr j) _ _ hr; exact fun e hv=> (hz e (((contains ..).mp hv).trans (hS.symm ▸ hx.trans (by omega)))).symm
  have he' : K=Aff.derivative T (till x) p g t := (Aff.derivative_range T (till x) p g hr t t₀ (fun i hi => hz i (hi.trans (show B≤m by omega)))).symm
  rw [← G.norm_adjoint (z i), map_sub, ← twist_bump P hP _ _ z w p,← Aff.derivative_gauge T (till x) p _ _ z hP]; rw [hi',he'] at Ht; exact Ht
end YM.PhysicalNext.InteractingRank.Milk
