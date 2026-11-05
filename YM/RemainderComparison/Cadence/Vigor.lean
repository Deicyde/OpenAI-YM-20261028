import YM.RemainderComparison.Cadence.Prune
import YM.Next.STATIONARY.Loops.Curvature
/-! # Exact kinetic matcher. p=2 chroma. Thermal LINEAR equals zero for Simple through actual critical solution & choice-independent Ward; no older-e here. α not yet conjugated by uncertainty in g. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Herbal
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D σ' C' D' W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G) (k': S.Choices) (ρ:Bid.Dir G c→AxisChart G F)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
variable {x:Positions (Uniform.Primary c G)}
variable (α₁ :ℝ)
local notation "f₀"=> Lapis.table F k' T.up T.high
local notation "F'"=> f₀ ∘ nod F ρ
local notation "H₁"=> (fun i:ℝ×Xs=> mainTerm T.low T.down (Herbal.sail F (Aux.nod F ρ i)))
local notation "H₂"=> (fun i:ℝ×Xs=> edict T.down T.low α₁ (Herbal.sail F (Aux.nod F ρ i)))
local notation "g₁"=> (thermal F k' T.high T.up ρ Θ)
local notation "g₂"=> (draft (c:=c) α₁ T.down T.low)
local notation "g₃"=> (fun x: Xs=> edict T.down T.low α₁ (represent (tint G _ x)))
local notation "h₁"=> Shellac.hum F T Θ ρ k'
local notation "h₂"=> Shellac.shed F T Θ ρ α₁ k'
local notation "W'"=> h₁-(fun _=>h₁ 0)
local notation "w"=> (h₁)-(fun _=>h₁ 0)
variable (hP:T.up.Bounds T.high σ C D)(hQ:T.down.Bounds T.low σ' C' D')
    (hc:Critical F T.high T.up ρ) (hG:G.Simple) (hO:LocalRatio Θ)
    (he:S.patch.Branches S.kernel G) (h₀:0<a)(hgap:PriceGap F T.high T.up a)
    (hp:ClassicalMatch F T.high T.low T.up T.down ρ)
variable (G': Golf (Lapis.table F k' T.up T.high) (mist F Θ T.up) (Lapis.orbit F ρ)
    (Lapis.gram F T.up T.high ρ k') n W u u Z)
open Stationary WilsonStartup.Change
include hp
lemma violet (x:Xs): Matches 4 F' H₁ (0,x):= by
    let E':ℝ×Xs→Bid.Dir G c:=fun x=> tint G _ (x.1 • x.2)
    have hx : E' (0,x)=0:=by simp [E']
    let M x:=mainTerm T.low T.down (represent (x:Bid.Dir G c)); let Φ x:=tested F k' T.high T.up x (ρ x)
    have hv:F'=Φ ∘ E':= by funext x; change Lapis.table F k' T.up T.high (nod F ρ x)=_; unfold Aux.nod Germ.usage Germ.kite Lantern.visit; simp only [smul_zero,add_zero]; rfl
    rw [hv]; exact (show Matches 4 Φ M (E' (0,x)) from (hx.symm ▸ (show Matches 4 Φ M 0 from ⟨(hp 0 (by omega) k').1,(hp 0 (by omega) k').2.1,fun i hi=>(hp i hi k').2.2⟩))).comp_refl (by exact ((tint G (Exterior.Body 1 c)).contDiff.contDiffAt.comp _ (contDiffAt_fst.smul contDiffAt_snd)))
omit hp
include hP hc hO hG he hgap h₀
lemma turbine : ContDiffAt ℝ ω (g₁) 0 ∧ iteratedFDeriv ℝ 1 (g₁) 0=0:=by
     let F₀:= victory F k' T.high T.up ρ; let C:= honorarium F k' 1 T.high T.up ρ; let M:= burnished F T.up ρ; let E:=arm G c 1; let A:=g₁
     have hp : A ∘ E =ᶠ[𝓝 0] M+C:= (Stationary.tribute hc he hP hgap h₀ zero_lt_one k' hO).mono fun a ht => ht.2
     obtain ⟨-,ht,hb⟩:= campaign hc he hP k' hgap h₀ (μ:=1) zero_lt_one hO
     let B:= E.symm
     have hv : A=(A ∘ E) ∘ B:=by funext x; simp [B]
     have hy : ContDiffAt ℝ ω A 0:= hv ▸ ((show ContDiffAt ℝ ω (A ∘ E) (B 0) by rw [map_zero]; exact ((hb.add ht).analytic.contDiffAt.congr_of_eventuallyEq hp)).comp (f:=B) _ B.contDiff.contDiffAt)
     refine ⟨hy,?_⟩
     change iteratedFDeriv ℝ 1 A 0=0
     ext1 u
     rw [hv,iteratedFDeriv_one_apply, fderiv_comp _ (by rw [map_zero]; exact (show ContDiffAt ℝ ω (A ∘ E) 0 from (by exact (hb.add ht).analytic.contDiffAt.congr_of_eventuallyEq hp)).differentiableAt (by simp)) B.differentiableAt,map_zero,hp.fderiv_eq]
     have hg:= point_quiet hG (hb.add ht) 1 (by norm_num) (by norm_num)
     have hh : ‖fderiv ℝ (M+C) 0‖=0:=by rw [← norm_iteratedFDeriv_one,hg,norm_zero]
     rw [norm_eq_zero.mp hh]; simp
omit hP hc hO hG he hgap h₀
include hQ
lemma pledge : Matches 2 g₃ (g₂ ∘ tint G _) 0∧ g₂ 0=0:= by
    let A:=tint G (YM.Exterior.Body 1 c)
    let M x:=mainTerm T.low T.down (represent (x:Bid.Dir G c)); let Q x := secondTerm T.low T.down (represent (x:Bid.Dir G c)); let L x:= Precision.loop T.down (represent (x:Bid.Dir G c)); let W:= (g₂); let P:= T.down
    obtain ⟨hm,hL⟩:= Extension.UV.LoopRate.rooted T.down (f:=c) T.low ⟨_,_,_,hQ⟩
    have ht:Matches 2 (α₁ • M + L) W (A 0) := by
       rw [map_zero]; exact ((show Matches 2 M Q 0 from hm).refl_comp (u:=fun i:ℝ=>α₁*i) (contDiffAt_const.mul contDiffAt_id)).add (matches_self _ hL.left)
    refine ⟨ht.comp_refl (f:=A) A.contDiff.contDiffAt,?_⟩
    have hv: Q 0=0:=by
       change Herbal.center T.down T.low (represent (0: Bid.Dir G c))=0
       rw [link_one]; simp [Herbal.center,Oriented.averaged,Herbal.still_turn]
    have he: L 0=0:=hL.value; change α₁ * Q 0 + L 0=0; simp [hv,he]

local notation "iP"=> (show Xs →ℝ from g₃-W')
variable {T' M γ κ :ℝ}(hM:1≤ M)(hX:(Fintype.card (Uniform.Primary c G):ℝ) ≤ M) (hs:(Fintype.card (Site c):ℝ)≤ M)
   (H':FiniteBound F T.up T.down T.high T.low α₁ Θ ρ T' γ κ) (hg:0<T')(hK: 0≤κ)
include hP hQ hc hG hO hM hX hs G' he h₀ hgap H' hg hK
local notation "q" => tollS M 2 (Shellac.sailAmt M G*(T'*κ*Real.exp (-γ*c.val)))
lemma rainy : ContDiffAt ℝ ω (iP) 0 ∧ (iP) 0=0∧ iteratedFDeriv ℝ 1 iP 0=0 ∧ normJ 2 (iP) 0 ≤ q:=by
    have hh:= Shellac.thermalP F T Θ ρ k' G' hO hc.1
    obtain ⟨hp₁,hp₂⟩:= pledge T α₁ hQ
    let H:= (h₁); let K:= g₃; let L':=(tint G (Exterior.Body 1 c)); let D:= g₂ ∘ L'; let Wz:= K-(H-fun _=>H 0)
    obtain ⟨hu,hU⟩:= turbine T F Θ k' ρ hP hc hG hO he h₀ hgap -- arg order
    change Matches 2 K D 0 at hp₁
    have hv : ContDiffAt ℝ ω H 0 := ((show ContDiffAt ℝ ω (g₁) (L' 0) by rw [map_zero]; exact hu).comp (f:=L') _ L'.contDiff.contDiffAt).congr_of_eventuallyEq hh.symm
    change ContDiffAt ℝ ω _ 0 ∧ Wz 0 =0 ∧ _
    refine ⟨hp₁.left.sub (hv.sub contDiffAt_const),?_,?_,?_⟩
    · change K 0-(H 0-H 0)=0; rw [sub_self,sub_zero]; exact hp₁.value.trans ( (congr_arg _ (L'.map_zero)).trans hp₂)
    ·
      have hx : iteratedFDeriv ℝ 1 D 0=0:=by
        let E:= L'.toContinuousLinearMap -- pointwise stationarity g₂ from gauge.
        let W:= arm G c 1; let L:= W.symm; let Hz₁:= stain_knit T.down T.low hQ (m:=c); let Hz₂:= stain_ink T.down.loop hQ.width hQ.two (fun i=>(hQ.invariant i).1) (m:=c)
        let Z:= (g₂ ∘ W)
        have hZ: Pointwise Z:= (Hz₁.coin α₁).add Hz₂
        have hy : iteratedFDeriv ℝ 1 Z 0=0:= point_quiet hG hZ _ (by norm_num) (by norm_num)
        have ht : D = Z ∘ L.toContinuousLinearMap ∘ E:= by funext x; change g₂ (E x)= g₂ (W (W.symm _)); rw [W.apply_symm_apply]
        let P:= L.toContinuousLinearMap.comp E
        rw [ht]; change iteratedFDeriv ℝ 1 (Z ∘ P) 0=0; rw [linear_pull P (by rw [map_zero]; exact hZ.analytic.contDiffAt),map_zero,hy]; ext1; rfl
      have hz : iteratedFDeriv ℝ 1 H 0=0:= by
         let E:=L'.toContinuousLinearMap
         rw [← (hh.iteratedFDeriv ℝ 1).self_of_nhds]; change iteratedFDeriv ℝ 1 (g₁ ∘ E) 0=0
         rw [linear_pull E (by rw [map_zero]; exact hu.of_le le_top),map_zero,hU]; ext1; rfl
      have h : (iP)=K-(H-(fun _=>H 0)):= rfl
      rw [h]; rw [iteratedFDeriv_sub_apply (g:=H-(fun _=>H 0)) (show ContDiffAt ℝ (1:ℕ) K 0 from hp₁.left.of_le le_top) ((hv.sub contDiffAt_const).of_le le_top), iteratedFDeriv_sub_apply (hv.of_le le_top) contDiffAt_const]; rw [hp₁.jets 1 (by omega),hx,hz,iteratedFDeriv_succ_const,Pi.zero_apply]; simp
    · have hp:= Shellac.sputter F T Θ ρ α₁ k' G' hM hX hs H' hc.1 hO hg hK
      change ‖iteratedFDeriv ℝ 2 (K-(H-(fun _=>H 0))) 0‖ ≤ _
      change ‖iteratedFDeriv ℝ 2 (D-H) 0‖≤ _ at hp
      rw [iteratedFDeriv_sub_apply (g:=H-(fun _=>H 0)) (hp₁.left.of_le le_top) ((hv.sub contDiffAt_const).of_le le_top), iteratedFDeriv_sub_apply (hv.of_le le_top) contDiffAt_const,iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]; rw [iteratedFDeriv_sub_apply (hp₁.right.of_le le_top) (hv.of_le le_top)] at hp; rw [hp₁.jets _ le_rfl]; exact hp
end YM.RemainderComparison.Cadence
