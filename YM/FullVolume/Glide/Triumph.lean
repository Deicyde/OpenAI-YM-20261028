import YM.FullVolume.Glide.Coincide
/-! One-step norms & betas. On Common orbit, not required balanced. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark.Glide
open Function Filter Set MeasureTheory Lattice RG Pressure RG.Shoot Wilson Precision RG.Supply Input Org
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Song Geo
open ConnectedActivityE6
open Push.PriceCompiler Further.StrongStartup UniformSpace
open WilsonStartup Progress.DirectedRecipe Time UVNext.CouplingReset Roof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A} {p m N n:ℕ}
open Muse Pass FullVolume.Urns FullVolume.Shadow FullVolume.Amp
variable {t ξ w d q:ℝ} {L:Lyrics R t t}
    (Y:Plato L q w d ξ)(O:Ops L N p)
-- layout norm at all periods does not forget Reads; val if proof.
local notation "Ω"=> A.B.a.clock.hatBeta
local notation "B"=> A.B.a
local notation "K"=> A.B.kin
namespace Window
open Contest
variable (h:Stationary.Artes.Cadre A.post A.B.kin)(he: Next.Free.Amplify A.B.M)(hp:Jams.Wild R.shape A.delay) {u:ℕ→ℕ}(hU:Tendsto u atTop atTop) {f:ℕ→ℝ}
   (P:∀ i,Contest (u i) p L)(Q:∀ i,Ops L (u i) p)
include h he hp Y hU
lemma bankA (hA:∀ j,Tendsto (fun i=>saga (P i) j) atTop (𝓝 (f j))):∃ X' g,Banked Y P Q f X' g:=by
    have hk j: Glints atTop (fun i=>saga (P i) j) (fun i=>saga (P i) j):=⟨_,hA j,hA j⟩; choose X' hx hX using fun j=> aglow Y h he hp hU hU hk (fun i=> cageM Y (Q i) (P i)) (fun i=>cageM Y (Q i) (P i)) j; choose g hg h' using fun j=> scored Y h he hp hU hU hk (fun i=> cageM Y (Q i) (P i)) (fun i=>cageM Y (Q i) (P i)) j; exact ⟨X',g,⟨hA,hx,hg⟩⟩
omit he hp h in
lemma thinning : ∃ g:ℕ→ℕ,StrictMono g∧ ∃ k:ℕ→ℝ,∀ i,Tendsto (fun n=> saga (P (g n)) i) atTop (𝓝 (k i)):=by
    let f n i:= saga (P n) i; have he i :∃ z:ℝ,∀ n, ‖f n i‖ ≤ z:=by
        let w:=normedWidth (Ω i); have hw:0<w:= widthP (Y.largeG.scale _|>.floor); let b₀:= (23/20:ℝ)/w
        have hk: ∀ᶠ n in atTop,‖f n i‖ ≤ b₀:= (hU.eventually_ge_atTop i).mono fun n hn=> by
               have hx:= mildS Y (P n) i hn; have hh:|w*f n i| ≤ 23/20:=abs_le.mpr ⟨le_trans (by norm_num) hx.1,hx.2⟩; apply (le_div_iff₀ hw).2; rw [mul_comm]; rwa [abs_mul,abs_of_nonneg hw.le] at hh
        obtain ⟨N,hN⟩:=eventually_atTop.mp hk; obtain ⟨C,hC⟩:= ((finite_Iic N).image (fun n=> ‖f n i‖)).bddAbove; exact ⟨max b₀ C,fun n=> le_total N n|>.elim (fun h=>le_max_of_le_left (hN n h)) (fun h=> le_max_of_le_right (hC ⟨_,h,rfl⟩))⟩
    choose b hb using he; obtain ⟨x,hx,k,hk,h⟩:= (isCompact_pi_infinite (fun i=>isCompact_Icc (a:=-b i) (b:=b i))).tendsto_subseq (x:=f) fun n i=> abs_le.mp (hb i n); exact ⟨k,hk,x,tendsto_pi_nhds.mp h⟩
lemma awaiting : ∃ g:ℕ→ℕ,StrictMono g ∧ ∃ f X g',Banked Y (fun i=> P (g i)) (fun i=> Q (g i)) f X g':=by
    obtain ⟨g,hg,k,hk⟩:= thinning Y hU P; exact ⟨g,hg,k,bankA Y h he hp (hU.comp hg.tendsto_atTop) (fun i=> P (g i)) (fun i=> Q (g i)) hk⟩
lemma allB {b:ℝ}(hP:Tendsto (fun n=> bonusB (P n)) atTop (𝓝 b)) : ∃ f X g,Banked Y P Q f X g :=by
    obtain ⟨r,hr,f,X',g',hX⟩:= awaiting Y h he hp hU P Q; refine ⟨f, bankA Y h he hp hU P Q (fun i=>Stationary.Artes.travels (fun t ht=>?_))⟩
    obtain ⟨s,hs,k,W,g,h'⟩:= awaiting Y h he hp (hU.comp ht.tendsto_atTop) (fun i=>P (t i)) (fun i=>Q (t i))
    let P':=fun i=> P (t (s i)); have hv:= ht.comp hs; have hf := (accord h he hp (hU.comp hv.tendsto_atTop) (hU.comp hr.tendsto_atTop) (u:=fun i=> u (t (s i))) (P:=P') h' hX ⟨_,hP.comp hv.tendsto_atTop,hP.comp hr.tendsto_atTop⟩ i).1
    exact ⟨s,hs,hf ▸ (h'.angles i)⟩
end Window
end YM.PhysicalNext.Repeat.Lark.Glide
#print axioms YM.PhysicalNext.Repeat.Lark.Glide.Window.allB
