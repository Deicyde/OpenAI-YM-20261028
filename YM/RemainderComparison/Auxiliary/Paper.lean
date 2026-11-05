import YM.RemainderComparison.Auxiliary.Proxy

/-!
 # Kinetic and common scalar part of the pre-exponential integral, in X.
 `tower` factors out actual volume price (not claimed polynomial uniformly
 at infinite volume!). Logs of determinants left on same programmatic β.
 Expensive action degree -2 includes the leading kinetic. ζ grading is
 literally powers of g in `drafting`, whose W inputs use this chart. No
 extraction/readjustment into previous calibration yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aux
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token
open YM.RemainderComparison.Exchange
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {p q w t : ℝ→ℝ}
variable {r j n : ℕ}
variable {c f : Side} {S : StepData c f}
variable (T : Tube G S) (F : Forest S.ratio) (Θ : ChartRatio G) (k : S.Choices) (ρ : Bid.Dir G c→AxisChart G F)
local notation "Q₀" => Lapis.gram F T.up T.high ρ k
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "ϕ" => Lapis.table F k T.up T.high
local notation "ψ" => Lapis.mist F Θ T.up
local notation "γ" => Lapis.orbit F ρ

def nod := usage (γ) 0
local notation "S'" => nod F ρ
local notation "𝔄" => ϕ ∘ nod F ρ
-- `plus pending` uses the SECOND-valuation including all b grades

def drafting (x:ℝ×Xs) := Trace.pending (ϕ ∘ S') 1 x+ (ψ (S' x)-ψ (S' 0))+(Lantern.shade Q₀ (x.1 • x.2)-Lantern.shade Q₀ 0)

def prominence (j : ℕ) (D A u:ℝ) := clump (j+2) (canopy' (j+2) D u A) A
def relay (j : ℕ) (D A u : ℝ) := prominence j D A u+(prominence j D A u+prominence j D A u)+clump j (wind j u) A
lemma relay_growth (j:ℕ) (hp:Reserve G L p) (ha:Reserve G L q) (hu:Reserve G L w) : Reserve G L fun t=> relay j (p t) (q t) (w t) := by
  have hr (j : ℕ) : Reserve G L fun t=> wind j (w t):= Reserve.mul (Reserve.mul (Reserve.const _) ((Reserve.const _).add hu)) (Reserve.const _)
  have hq:= ((Reserve.const 1).add ha).add hp
  have hv:Reserve G L fun x=> prominence j (p x) (q x) (w x) := Reserve.comp _ (Reserve.comp _ ((hr (j+2)).add (hr _)) (hq.add hq)) ha
  exact (hv.add (hv.add hv)).add (Reserve.comp j (hr _) ha)
variable {u a P D d p' v : ℝ}
variable (B : BudgetPoint) (β : ℝ)
local notation "g" => gStep β

def faceUp (y:Xs) := coverLog F T Θ k ρ β (g•y)-coverLog F T Θ k ρ β 0
local notation "Ω" => faceUp T F Θ k ρ β
variable {x:Positions (Uniform.Primary c G)} (h : Pilot T F Θ k ρ B β D d a P p' n x) (hz : v ≤ d) (hg : v*u ≤ d) (hm:0<v) (hu:0<u)
local notation "🞂" => Germ.patch Xs v u
include h hg hz hm hu
lemma inkWeight {i:ℕ} (hi:i+2≤n) (y:ℝ×Xs) (hy:y∈Germ.patch Xs v u) : Brush i (relay i D p' u) 1 (drafting T F Θ k ρ) y := by
  have hP:= h.core
  have hh : ‖(0:Y)‖≤D:= by rw [norm_zero]; exact hP.off
  let Γ : ℝ×Xs→ℝ :=𝔄; let G':=ψ ∘ S'; let p:= prominence i D p' u
  have hp y (hy:y∈ 🞂) : Brush (i+2) p 1 Γ y ∧ Brush (i+2) p 1 G' y:= by
    obtain ⟨hf,hK⟩:=(patch_test ..).1 (kite_moves hz hg hy)
    have he:=hP.color 0 1 (kite y) hh (by simp) hf hK
    have ht:= arrangement hP hi hz hg hy hh
    exact ⟨composite ht (he.1.smaller (by omega)),Lantern.composite ht (he.2.smaller (by omega))⟩
  have H: Brush i p 1 (Trace.pending Γ 1) y:= Trace.work _ _ _ ((show ∀ᶠ q in 𝓝 y,q∈ 🞂 from (patch_open ..).mem_nhds hy).mono fun i hi t ht=> (hp _ (Germ.keeps hi ht)).1)
  have hf:= aileron (j:=i) (hz.trans hP.small) hy |>.1
  have hs:= hP.gram _ (((patch_test ..).1 (kite_moves hz hg hy)).2)
  have hw : ((0:ℝ),(0:Xs))∈ 🞂:= (patch_test ..).2 ⟨norm_zero.trans_lt hm,norm_zero.trans_lt hu⟩
  have hy' := hp y hy|>.2; have hu : Brush i p 1 (fun _ : ℝ×Xs=> ψ (S' 0)) y:= (Brush.certified zero_le_one _).climb (hp _ hw|>.2.bound) le_rfl
  exact (H.gathering ((hy'.smaller (by omega)).separating hu)).gathering (composite hf (hs.2.smaller (by omega)))

lemma ideal (hi : 2≤n) (hβ : 0<β) (x':Xs) (hx' : (g,x')∈Germ.patch Xs v u) : Ω x'=drafting T F Θ k ρ (g,x') := by
  let y:=(g,x'); let z:=y.1 • y.2
  have hf : (S') y=(z,γ z):= by simp [nod,usage,kite,Lantern.visit,z]
  have hx : (S') (0,x')=0 := by rw [nod, usage, Lantern.visit]; simp [kite,h.origin]
  have hh:(S') 0=(0,γ 0):= by unfold nod usage Lantern.visit kite; simp
  have hP:=h.core; let F₀:=ϕ; let F':=ϕ ∘ nod F ρ
  have hd : ‖(0:Y)‖ ≤ D:= norm_zero.trans_le hP.off
  have hv' z (hz' : z∈ 🞂) : Brush 2 (canopy' 2 D u p') 1 (nod F ρ) z ∧ ContDiffAt ℝ 2 ϕ (nod F ρ z) := by
    have he := (patch_test ..).1 (kite_moves hz hg hz')
    have hv:= hP.color 0 1 (kite z) hd (by simp) he.1 he.2
    refine ⟨arrangement hP hi hz hg hz' hd,?_⟩
    exact_mod_cast (hv.1.smaller (by omega : 2≤n+2)).smooth
  have he₀ := hv' ((0:ℝ),(0:Xs)) (show (0,(0:Xs))∈Germ.patch Xs v u from ⟨mem_ball_self hm,mem_ball_self hu⟩)
  have He : ((0:ℝ),x')∈ 🞂:= (patch_test ..).2 ⟨norm_zero.trans_lt hm, ((patch_test ..).1 hx').2⟩
  have he:= hv' _ He
  have hc : Germ.cleared F' 2 (0,x'):= chart_cleared F₀ h.shore (by simpa only [hx,Nat.cast_ofNat] using he.2) _ _ hx he.1.smooth
  have hp :ϕ (z,γ z)=g^2* Trace.pending F' 1 (g,x'):= by
    have hQ:= Trace.quote F' 1 (b:=g) (x:=x') fun t ht=> by
      have he := hv' _ (keeps hx' ht); norm_num only [Nat.reduceAdd,Nat.cast_ofNat]; exact he.2.comp _ (he.1.smooth.of_le (by norm_num))
    rw [Germ.free (a:=(g,x')) F' hc,zero_add] at hQ
    rw [← hf]; exact hQ
  have ht : ϕ (0,γ 0)=0:= by
    rw [h.origin]
    have hx := congr_arg (fun G: (Xs×Y) [×0]→L[ℝ] ℝ=> G 0) (h.shore 0 (by decide)); exact hx
  have hg₀ : β*ϕ (z,γ z)=Trace.pending F' 1 (g,x'):= by rw [hp,← mul_assoc,mul_comm β,Fare.gS _ hβ|>.2,one_mul]
  unfold faceUp coverLog drafting; change β *ϕ (z,γ z)+_+ _- _= _
  rw [hg₀,ht,show S' (g,x')=(z,γ z) from hf,hh]
  unfold F'; dsimp only [z,y]; ring_nf

lemma reflection (hi:j+(r+1)+2≤n) (hβ:0<β) {x':Xs} (hx' : (g,x')∈ 🞂) : Queue (drafting T F Θ k ρ) (Ω) g x' v u j r (relay (j+(r+1)) D p' u) := by
  have hs z (he:z∈ 🞂):= inkWeight T F Θ k ρ B β h hz hg hm hu hi z he; have hf:= Fare.gS β hβ ; let V':= relay (j+(r+1)) D p' u; have hr : 0 ≤ V':= (hs _ hx').nonneg
  refine ⟨hr,hx',hf.1,hs, ?_⟩
  have hp : 0 ≤ g^(r+1)*V' := by have hx:=hf.1; positivity
  refine ((Brush.certified (k:=j) zero_le_one (x:=x') (0:ℝ)).climb (hp.trans' (by rw [norm_zero])) le_rfl).shimmy ?_
  filter_upwards [(show Tendsto (fun x':Xs=>(g,x')) (𝓝 x') (𝓝 (g,x')) from continuousAt_const.prodMk continuousAt_id).eventually (show ∀ᶠ y in 𝓝 (g,x'), y∈ 🞂 from (patch_open ..).mem_nhds hx')] with y hy; rw [ideal T F Θ k ρ B β h hz hg hm hu (by omega) hβ y hy,sub_self]
end YM.RemainderComparison.Aux
